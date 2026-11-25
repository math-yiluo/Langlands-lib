/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.DiagonalEndpointsProof.DiagonalLimitEndpointsAux

/-! # A normalized isomorphism between strict root systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- Each level of a restricted strict system is killed by `l ^ (n + 1)`. -/
theorem restriction_pow_smul_eq_zero (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : ((r.F.obj M).obj (op n)).obj.obj U) :
    (l ^ (n + 1)) • x = 0 := by
  have h := r.scalars M n U (l ^ (n + 1)) x
  have hz : PadicInt.toZModPow (n + 1) ((l : ℤ_[l]) ^ (n + 1)) = 0 := by
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  change ((l : ULift.{u + 1} ℤ_[l]) ^ (n + 1)) • x =
    ((PadicInt.toZModPow (n + 1)) ((l : ℤ_[l]) ^ (n + 1))).val • x at h
  rw [hz, ZMod.val_zero, zero_nsmul] at h
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using h

/-- An additive map into a level of a restricted strict system, viewed as a map of
`ℤ_[l]`-module sheaves. Linearity holds because the target is killed by `l ^ (n + 1)`. -/
def liftToRestriction (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (n : ℕ)
    (Q : DiagonalMod l T)
    (f : (diagonalForget l T).obj Q ⟶
      (diagonalForget l T).obj ((r.F.obj M).obj (op n))) :
    Q ⟶ (r.F.obj M).obj (op n) :=
  ObjectProperty.homMk
    { app U := by
        let g : Q.obj.obj U →+ (((r.F.obj M).obj (op n)).obj.obj U) := (f.hom.app U).hom
        exact ModuleCat.ofHom
          { toFun := g
            map_add' := g.map_add
            map_smul' z x := DiagonalEndpointsProof.padic_map_smul_target (n + 1)
              (restriction_pow_smul_eq_zero l T r M n U) g z x }
      naturality U V g := by
        apply (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
          AddCommGrpCat.{u + 1}).map_injective
        exact f.hom.naturality g }

/-- The strict-system map lifting the additive root identification
`roots.hom ≫ k.lineForget.inv` levelwise along `liftToRestriction`. -/
def diagonalTraceNormalizedRootHom (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) :
    H ⟶ r.F.obj (lineModule l (ULift.{u} (Padic l)) c) where
  app n := liftToRestriction l T r _ n.unop (H.obj n) ((roots.hom ≫ k.lineForget.inv).app n)
  naturality n m f := by
    ext U x
    exact congrArg (fun a ↦ a.hom.app U x) ((roots.hom ≫ k.lineForget.inv).naturality f)

theorem whiskerRight_diagonalTraceNormalizedRootHom (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) :
    Functor.whiskerRight (diagonalTraceNormalizedRootHom l T c r k H roots)
      (diagonalForget l T) = roots.hom ≫ k.lineForget.inv := by
  ext n U x
  rfl

/-- The lifted root identification is an isomorphism of strict systems.
Source: diagonal tower trace proof (1), root-system identification, and the scalar
restriction convention in the geometric classes construction.
(blueprint: lem-sfb-diagonal-trace-normalized-root-iso).

Proof: the restricted target at level n is killed by l^(n+1). An additive map into
such a target is Z_l-linear: approximate a scalar by an integer modulo l^(n+1)
and the error term acts by zero. Apply this to roots.hom followed by
k.lineForget.inv. Faithfulness proves naturality, and reflection of isomorphisms
by forgetting scalars makes the resulting strict-system map invertible. -/
instance isIso_diagonalTraceNormalizedRootHom (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) :
    IsIso (diagonalTraceNormalizedRootHom l T c r k H roots) := by
  have : (diagonalForget l T).ReflectsIsomorphisms := by
    unfold diagonalForget
    infer_instance
  have (n : ℕᵒᵖ) : IsIso ((diagonalTraceNormalizedRootHom l T c r k H roots).app n) := by
    have he : (diagonalForget l T).map ((diagonalTraceNormalizedRootHom l T c r k H roots).app n) =
        (roots.hom ≫ k.lineForget.inv).app n :=
      NatTrans.congr_app (whiskerRight_diagonalTraceNormalizedRootHom l T c r k H roots) n
    have : IsIso ((diagonalForget l T).map
        ((diagonalTraceNormalizedRootHom l T c r k H roots).app n)) := by
      rw [he, NatTrans.comp_app]
      infer_instance
    exact isIso_of_reflects_iso _ (diagonalForget l T)
  exact NatIso.isIso_of_isIso_app _

/-- The normalized isomorphism between the strict root system `H` and the restricted
line module, lifting `roots.hom ≫ k.lineForget.inv`.
(blueprint: lem-sfb-diagonal-trace-normalized-root-iso). -/
def diagonalTraceNormalizedRootIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) :
    H ≅ r.F.obj (lineModule l (ULift.{u} (Padic l)) c) :=
  asIso (diagonalTraceNormalizedRootHom l T c r k H roots)

theorem whiskerRight_diagonalTraceNormalizedRootIso_hom (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) :
    Functor.whiskerRight (diagonalTraceNormalizedRootIso l T c r k H roots).hom
      (diagonalForget l T) = roots.hom ≫ k.lineForget.inv :=
  whiskerRight_diagonalTraceNormalizedRootHom l T c r k H roots

end AlgebraicGeometry.ProEtale.DiagonalTrace
