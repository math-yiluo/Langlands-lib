/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-! # Exactness of the closed Cech presentation on the closed fibre
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The closed Čech presentation is exact after restriction to the closed fibre, for an
arbitrary pro-étale object `V` and an arbitrary finite family `U` over it. -/
theorem closedCech_closed_restriction_exact
    (A : Type u) [CommRing A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) {n : ℕ} (U : Fin n → Over V)
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A b P V U) q) :
    (T.complex.map (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) b.closedComplement)).Exact := by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let i := b.closedComplement
  let adj := ProEtale.upperStarLowerStarAdjunction Λ i
  refine ShortComplex.exact_of_forall_injective _ fun J _ φ hφ ↦ ?_
  let φ' := adj.homEquiv _ _ φ
  have hφ' : T.complex.f ≫ φ' = 0 := by
    rw [← adj.homEquiv_naturality_left]
    exact (adj.homEquiv _ _).symm.injective (by simpa using hφ)
  -- The Čech complex of the closed push-pull of `i_* J` is exact in positive degrees.
  have hinj : Injective ((ProEtale.upperStar Λ P.hom).obj ((ProEtale.lowerStar Λ i).obj
      ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J)))) := by
    have : IsIso adj.counit := ProEtale.isIso_upperStarLowerStarAdjunction_counit Λ i
    have : Injective ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J)) :=
      Injective.of_iso (asIso (adj.counit.app J)).symm inferInstance
    have : (ProEtale.lowerStar Λ i).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
    have : Injective ((ProEtale.lowerStar Λ i).obj
        ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J))) :=
      Functor.PreservesInjectiveObjects.injective_obj (F := ProEtale.lowerStar Λ i) inferInstance
    exact ProEtale.injective_upperStar_obj_of_weaklyEtale Λ P.hom _
  have hex : ((closedCechCoefficientFunctor A b P V U).obj
      ((ProEtale.lowerStar Λ i).obj J)).ExactAt (q + 1) := by
    obtain ⟨G, hG⟩ : ∃ G, G = (ProEtale.upperStar Λ P.hom).obj ((ProEtale.lowerStar Λ i).obj
        ((ProEtale.upperStar Λ i).obj ((ProEtale.lowerStar Λ i).obj J))) := ⟨_, rfl⟩
    rw [← hG] at hinj
    have : Injective G.obj := (sheafificationAdjunction _ _).map_injective _ hinj
    have h := Presheaf.exactAt_categoricalCech_of_injective G.obj U q
    subst hG
    exact h
  have hsc := (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)).1 hex
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1 hsc
    (T.middle _ φ') (by
      change ((closedCechCoefficientFunctor A b P V U).obj _).d (q + 1) (q + 2) _ = 0
      rw [← T.first_boundary, hφ', map_zero])
  refine ⟨(adj.homEquiv _ _).symm ((T.last _).symm c), ?_⟩
  change (ProEtale.upperStar Λ i).map T.complex.g ≫ _ = φ
  rw [← adj.homEquiv_naturality_left_symm]
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply (T.middle _).injective
  rw [T.last_boundary, AddEquiv.apply_symm_apply]
  exact hc

end AlgebraicGeometry.Scheme
