/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperLocalizingCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Canonical derived truncations preserve small coproducts. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem truncLE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) A]
    [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncLE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncLE a
  let ι := t.truncLEι a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    let c := sigmaComparison T K
    have hc : IsIso c := by
      apply (DerivedCategory.isIso_iff A c).2
      intro n
      let H := DerivedCategory.homologyFunctor A n
      by_cases hn : n ≤ a
      · have hi (M : DerivedCategory A) : IsIso (H.map (ι.app M)) := by
          have : ((t.triangleLEGT a).obj M).obj₃.IsGE (a + 1) :=
            t.isGE_truncGT_obj M a (a + 1)
          exact DerivedCategory.isIso_homologyMap_mor₁ _
            (t.triangleLEGT_distinguished a M) (n - 1) n (by omega)
            (DerivedCategory.isZero_of_isGE _ (a + 1) (n - 1) (by omega))
            (DerivedCategory.isZero_of_isGE _ (a + 1) n (by omega))
        have hleft : IsIso (Limits.Sigma.map (fun i ↦ H.map (ι.app (K i)))) := by
          infer_instance
        have hsquare : sigmaComparison H L ≫ H.map c ≫ H.map (ι.app (∐ K)) =
            Limits.Sigma.map (fun i ↦ H.map (ι.app (K i))) ≫ sigmaComparison H K := by
          apply Sigma.hom_ext
          intro i
          simp only [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc]
          rw [← H.map_comp, ← H.map_comp]
          rw [← Category.assoc, ι_comp_sigmaComparison]
          rw [ι.naturality, Functor.id_map, H.map_comp]
          simp only [Functor.id_obj, ι_comp_sigmaComparison]
        have : IsIso (sigmaComparison H L ≫ H.map c ≫ H.map (ι.app (∐ K))) := by
          rw [hsquare]
          infer_instance
        have : IsIso (H.map c ≫ H.map (ι.app (∐ K))) :=
          IsIso.of_isIso_comp_left (sigmaComparison H L) _
        exact IsIso.of_isIso_comp_right (H.map c) (H.map (ι.app (∐ K)))
      · have hsrc : IsZero (H.obj (∐ L)) :=
          (isColimitOfPreserves H (coproductIsCoproduct L)).isZero_pt
            (Functor.isZero _ fun i ↦ by
              have : (L i.as).IsLE a := t.isLE_truncLE_obj (K i.as) a a
              exact DerivedCategory.isZero_of_isLE (L i.as) a n (by omega))
        have htgt : IsZero (H.obj (T.obj (∐ K))) :=
          DerivedCategory.isZero_of_isLE _ a n (by omega)
        exact hsrc.isIso htgt (H.map c)
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

/-- Double good truncation preserves small coproducts.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window-ii general proof,
paragraph 1 (blueprint: lem-sfb-derived-truncation-coproducts).

Proof: exact coproducts of module sheaves imply that cohomology commutes with
derived coproducts. The comparison from the sum of upper truncations to the upper
truncation of the sum is an isomorphism on cohomology: in retained degrees it is
the sum of the canonical cohomology isomorphisms, and outside them both sides
are zero. Cohomology detects isomorphisms. For lower truncation, coproducts of
objects in D≥r remain there by the homology formula, and the universal property
of K→τ≥r K constructs the inverse comparison. Reuse the proved generic theorem
`CondensedRing.truncGE_preservesCoproducts` for this step. Composing the two
preservation statements proves the assertion.
For an empty family all sums and all their cohomologies are zero, so the same
argument applies. No boundedness or constructibility is required. -/
theorem derivedTruncation_preservesCoproducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (I : Type (u + 1)) (q r : ℤ) :
    PreservesColimitsOfShape (Discrete I)
      ((DerivedCategory.TStructure.t (C := pulledBackModuleObjects Λ X)).truncLE q ⋙
        DerivedCategory.TStructure.t.truncGE r) := by
  let A := pulledBackModuleObjects Λ X
  have : HasColimitsOfShape (Discrete I) A :=
    IsGrothendieckAbelian.hasColimitsOfShape_discrete A I
  have : HasExactColimitsOfShape (Discrete I) A :=
    IsGrothendieckAbelian.hasExactColimitsOfShape_discrete A I
  have : HasCoproducts.{u + 1} A := fun J ↦
    IsGrothendieckAbelian.hasColimitsOfShape_discrete A J
  have : HasCoproducts.{u + 1} (DerivedCategory A) := derived_hasCoproducts
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.TStructure.t.truncLE q) :=
    truncLE_preservesCoproducts (A := A) q
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.TStructure.t.truncGE r) :=
    CondensedRing.truncGE_preservesCoproducts (A := A) r
  infer_instance

end AlgebraicGeometry.ProEtale
