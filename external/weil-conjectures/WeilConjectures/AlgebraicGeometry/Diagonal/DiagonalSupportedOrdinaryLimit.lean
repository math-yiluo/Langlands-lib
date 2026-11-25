/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedQuotientCoefficientTower

/-! # The normalized ordinary limit of the supported quotient tower

Source: diagonal tower limit proof, paragraph (1), and Stacks Tag 099L.
(blueprint: lem-sfb-diagonal-supported-ordinary-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem padicLinearIntoTorsion {l : ℕ} [Fact l.Prime]
    {M N : Type (u + 1)} [AddCommGroup M] [Module (ULift.{u + 1} ℤ_[l]) M]
    [AddCommGroup N] [Module (ULift.{u + 1} ℤ_[l]) N]
    (n : ℕ) (hN : ∀ y : N, (l ^ n) • y = 0) (f : M →+ N)
    (r : ULift.{u + 1} ℤ_[l]) (x : M) : f (r • x) = r • f x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (r.down.appr_spec n)
  have hr : r - (r.down.appr n : ULift.{u + 1} ℤ_[l]) =
      (ULift.up a) * (l : ULift.{u + 1} ℤ_[l]) ^ n := by
    apply ULift.ext
    exact ha.symm
  have split (y : M) :
      r • y = (l ^ n) • (ULift.up a • y) + r.down.appr n • y := by
    conv_lhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{u + 1} ℤ_[l]), hr]
    rw [add_smul, mul_comm (ULift.up a), mul_smul]
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [split, map_add, map_nsmul, hN, zero_add, map_nsmul]
  conv_rhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{u + 1} ℤ_[l]), hr]
  rw [add_smul, mul_comm (ULift.up a), mul_smul]
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hN, zero_add]

private def liftTorsionMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M N : DiagonalMod l X) (n : ℕ)
    (hN : ∀ (U : X.ProEtᵒᵖ) (x : N.obj.obj U), (l ^ (n + 1)) • x = 0)
    (f : (diagonalForget l X).obj M ⟶ (diagonalForget l X).obj N) : M ⟶ N :=
  ObjectProperty.homMk
    { app U := by
        let g : M.obj.obj U →+ N.obj.obj U := (f.hom.app U).hom
        exact ModuleCat.ofHom
          { toFun := g
            map_add' := g.map_add
            map_smul' z x := padicLinearIntoTorsion (n + 1) (hN U) g z x }
      naturality U V g := by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }

private theorem quotientKilled (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (n : ℕ) : l ^ (n + 1) • 𝟙 ((D.E.obj (diagonalIntegralSource Y)).obj (op n)) = 0 := by
  have : Epi ((D.π n).app (diagonalIntegralSource Y)) :=
    Cofork.IsColimit.epi (D.quotient n (diagonalIntegralSource Y))
  apply (cancel_epi ((D.π n).app (diagonalIntegralSource Y))).mp
  simp only [Preadditive.comp_nsmul, comp_zero]
  erw [Category.comp_id]
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using
    D.zero n (diagonalIntegralSource Y)

/-- The completed supported constant is the ordinary limit of its quotient tower,
with the coefficient-unit normalization at every projection.

Source: blueprint latest, `sk-prop-diagonal-tower-limit.proof.md`, paragraph (1);
the cokernel source calculation in `sk-prop-diagonal-tower-system`, step (3);
Stacks Tag 099L.
(blueprint: lem-sfb-diagonal-supported-ordinary-limit).

Proof: extend the supported integral constant to constant Z_l coefficients.
The normalized supported scalar-extension isomorphism identifies this with the
supported constant Z_l-module. At level n, the coefficient quotient map has kernel
l^(n+1) and is an epimorphism. Exact closed direct image preserves its cokernel.
The cokernel universal property of D identifies each level, uniquely preserving
the quotient map, with that supported finite constant. The transition equations
of D make these identifications a natural isomorphism of towers. Closed direct
image preserves inverse limits, and forgetting module structure creates them.
The inverse limit of the finite constant coefficient rings is the actual
completed coefficient sheaf; its scalar action is the action restricted along
the canonical constant-to-completed coefficient map. Thus this tower limit is
the restriction of diagonalCompletedSource. Its map from the supported integral
constant takes an integer to that integer times one. The uniqueness assertion
for diagonalCompletedGenerator identifies this map with the named generator.
Composing the limit comparison with the n-th projection therefore recovers the
specified scalar-adjunction unit followed by D's quotient map. This construction
uses only the ordinary presentation, includes n=0, and on the empty scheme all
maps and objects are zero. No derived-limit or completeness assertion is used. -/
theorem diagonal_supported_ordinary_limit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y))) :
    ∃ s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)),
      ∀ n : ℕ,
        diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget l (diagonalSurface Y)).map
            ((D.π n).app (diagonalIntegralSource Y)) := by
  let F := diagonalForget l (diagonalSurface Y)
  let H := D.E.obj (diagonalIntegralSource Y)
  let M := (diagonalCompletedRestriction l (diagonalSurface Y)).obj
    (diagonalCompletedSource l Y)
  have : F.Faithful := by dsimp only [F, diagonalForget]; infer_instance
  have : F.ReflectsIsomorphisms := by dsimp only [F, diagonalForget]; infer_instance
  obtain ⟨e, he⟩ := diagonal_supported_quotient_coefficient_tower l Y D
  obtain ⟨a, ha⟩ := diagonal_supported_coefficient_limit l Y
  let b : F.obj M ≅ limit (H ⋙ F) := a ≪≫ HasLimit.isoOfNatIso e.symm
  let c : Cone H :=
    { pt := M
      π :=
        { app := fun n ↦ liftTorsionMap l (diagonalSurface Y) M (H.obj n) n.unop
            (by
              intro U x
              have h := quotientKilled l Y D n.unop
              exact ConcreteCategory.congr_hom
                (congrArg (fun f ↦ f.hom.app U) h) x)
            (b.hom ≫ limit.π (H ⋙ F) n)
          naturality := by
            intro i j f
            apply F.map_injective
            change 𝟙 _ ≫ (b.hom ≫ limit.π (H ⋙ F) j) =
              (b.hom ≫ limit.π (H ⋙ F) i) ≫ F.map (H.map f)
            rw [Category.id_comp, Category.assoc]
            exact congrArg (fun g ↦ b.hom ≫ g) (limit.w (H ⋙ F) f).symm } }
  let t := limit.lift H c
  have ht : F.map t ≫ (preservesLimitIso F H).hom = b.hom := by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, preservesLimitIso_hom_π, ← F.map_comp, limit.lift_π]
    rfl
  have ht' : F.map t = b.hom ≫ (preservesLimitIso F H).inv := by
    apply (cancel_mono (preservesLimitIso F H).hom).mp
    rw [ht, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsIso (F.map t) := by rw [ht']; infer_instance
  have : IsIso t := isIso_of_reflects_iso t F
  refine ⟨asIso t, ?_⟩
  intro n
  apply (cancel_mono (e.hom.app (op n))).mp
  change diagonalCompletedGenerator l Y ≫ F.map
      (t ≫ limit.π H (op n)) ≫ e.hom.app (op n) = _
  rw [F.map_comp, ← preservesLimitIso_hom_π F H]
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  dsimp only [b, Iso.trans_hom]
  simp only [Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π_assoc, Iso.symm_hom, Iso.inv_hom_id_app,
    Category.comp_id]
  exact (ha n).trans (he n).symm

end AlgebraicGeometry.ProEtale
