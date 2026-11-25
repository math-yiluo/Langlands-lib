/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalResidueDerivedFactorization

/-! # Exact quotient realization of restricted finite evaluation

Source: diagonal tower system proof (4), using the actual sheaf quotient construction.
(blueprint: lem-sfb-diagonal-trace-finite-residue-functor). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] diagonalFiniteToPadic

/-- Ordinary residue scalar restriction is fully faithful.
Source: surjective scalar restriction for module sheaves
(blueprint: lem-sfb-diagonal-trace-finite-residue-functor). -/
theorem finiteResidueRestriction_full_faithful (l n : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) :
    (diagonalFiniteToPadic l n T).Full ∧ (diagonalFiniteToPadic l n T).Faithful := by
  constructor
  · unfold diagonalFiniteToPadic
    exact Sheaf.restrictScalars_full _ _ (diagonalResidueProjection_surjective l n)
  · unfold diagonalFiniteToPadic
    infer_instance

private theorem restriction_killed (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : SpTowerClasses.Systems T (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T))
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : ((r.F.obj M).obj (op n)).obj.obj U) :
    (l ^ (n + 1)) • x = 0 := by
  have h := r.scalars M n U (l ^ (n + 1)) x
  have hz : PadicInt.toZModPow (n + 1) ((l : ℤ_[l]) ^ (n + 1)) = 0 := by
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  change ((l : ULift.{u + 1} ℤ_[l]) ^ (n + 1)) • x =
    ((PadicInt.toZModPow (n + 1)) ((l : ℤ_[l]) ^ (n + 1))).val • x at h
  rw [hz, ZMod.val_zero, zero_nsmul] at h
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using h

/-- Restricted evaluation factors through an exact residue functor.
Source: diagonal tower system proof (4)
(blueprint: lem-sfb-diagonal-trace-finite-residue-functor).

Proof: the scalar equation kills the positive prime power. The quotient projection is
epic and, by its exactness, monic on these objects. Its natural isomorphism identifies
scalar restriction of the quotient functor with the original exact evaluation.
Scalar restriction reflects isomorphisms, and therefore reflects its exactness. -/
theorem exactFiniteResidueFunctor_exists (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ) :
    ∃ (G : SpTowerClasses.Systems T
        (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (diagonalResidue.{u} l n)))
      (_ : G.Additive) (_ : PreservesFiniteLimits G) (_ : PreservesFiniteColimits G),
      Nonempty (G ⋙ diagonalFiniteToPadic l n T ≅
        r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n)) := by
  let V := r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n)
  let J := Scheme.ProEt.topology T
  let q := diagonalResidueProjection.{u} l n
  let F := diagonalFiniteToPadic l n T
  let a : ULift.{u + 1} ℤ_[l] := (l ^ (n + 1) : ℕ)
  let rd := Sheaf.reductionDatum J q (diagonalResidueProjection_surjective l n) a
    (diagonalResidueProjection_ker l n)
  let G := V ⋙ rd.Φ
  have hzero (M : SpTowerClasses.Systems T
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T)) :
      (Sheaf.smulNatTrans J a).app (V.obj M) = 0 := by
    ext U x
    dsimp
    erw [NatTrans.app_smul]
    change a • x = 0
    simpa only [a, Nat.cast_smul_eq_nsmul] using restriction_killed l T r M n U x
  have hiso (M : SpTowerClasses.Systems T
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T)) :
      IsIso (rd.r.app (V.obj M)) := by
    have := rd.epi_r (V.obj M)
    have := (rd.exact (V.obj M)).mono_g (hzero M)
    exact isIso_of_mono_of_epi _
  let η := Functor.whiskerLeft V rd.r
  have : ∀ X, IsIso (η.app X) := fun X ↦ hiso X
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let e0 : G ⋙ Sheaf.restrictScalars J q ≅ V :=
    Functor.associator V rd.Φ _ ≪≫ (asIso η).symm ≪≫ Functor.rightUnitor V
  let e : G ⋙ F ≅ V := by
    unfold F diagonalFiniteToPadic
    exact e0
  have : PreservesFiniteLimits (G ⋙ F) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (G ⋙ F) := preservesFiniteColimits_of_natIso e.symm
  have : F.ReflectsIsomorphisms := by unfold F diagonalFiniteToPadic; infer_instance
  have : PreservesFiniteLimits G := preservesFiniteLimits_of_reflects_of_preserves G F
  have : PreservesFiniteColimits G := preservesFiniteColimits_of_reflects_of_preserves G F
  exact ⟨G, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
