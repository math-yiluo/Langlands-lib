/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelProEtaleLocalIsoSections
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelEtaleLocalRepresentative

/-! # Local isomorphism representatives for a finite-level model

## References

* Stacks Project, Tags 099Y, 099Z, 09B1 and 09BV
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The comparison and local model hypotheses produce an étale representative of an
isomorphism at every geometric point. -/
theorem lisse_finite_level_etale_local_isomorphisms
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hDbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj D))
    (hDlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj D))
    (hcomparison : Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((localIsomorphismRestriction U.left
          (lisseTowerEtaleRing d n) V).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E) ≅
          (localIsomorphismRestriction U.left
            (lisseTowerEtaleRing d n) V).obj D) := by
  have hsections :=
    lisse_finite_level_proetale_local_iso_sections X Y g d U n N E D
      hDbounded hDlisse hcomparison hmodels
  have hDplus : DerivedCategory.TStructure.t.plus D := by
    obtain ⟨a, b, hab⟩ := hDbounded
    exact ⟨a, (DerivedCategory.isGE_iff D a).2 (fun q hq ↦ hab q (Or.inl hq))⟩
  exact exists_etale_local_representative_of_proetale_local_iso_sections Y U
    ((normalizationConstant U.left.smallEtaleTopology).obj E) D hDplus hsections

end AlgebraicGeometry.Scheme
