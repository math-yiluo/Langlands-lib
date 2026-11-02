import Langlands.AlgebraicGeometry.Picard.FractionFieldBundleExtension
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Actual bundle extension over a Noetherian valuation domain -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
  [IsNoetherianRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (A : AbelianScheme (Spec (CommRingCat.of R)))
  (D : LineBundle (mumfordProduct
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left)

/-- An actual extension and restriction isomorphism over every Noetherian
valuation domain, including fields. No axis-triviality premise is needed. -/
def noetherianValuationRingSelfProductExtension :
    Σ E : LineBundle (mumfordProduct A).left,
      ((LineBundle.pullback (mumfordProductBaseChangeMap A
        (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj E).obj ≅ D.obj :=
  Classical.choice <| by
    classical
    by_cases hR : IsField R
    · obtain ⟨E, ⟨e⟩⟩ := selfProductLineBundleExtension_of_isField R K hR A D
      exact ⟨⟨E, e⟩⟩
    · have : IsDiscreteValuationRing R :=
        { not_a_field' := fun h =>
            hR (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h) }
      obtain ⟨E, ⟨e⟩⟩ := discreteValuationRingSelfProductLineBundleExtension R K A D
      exact ⟨⟨E, e⟩⟩

/-- Every generic self-product bundle extends over a Noetherian valuation
domain along the specified fraction-field product map. -/
theorem selfProductLineBundleExtension_of_noetherianValuationRing :
    ∃ E : LineBundle (mumfordProduct A).left,
      Nonempty (((LineBundle.pullback (mumfordProductBaseChangeMap A
        (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj E).obj ≅ D.obj) :=
  ⟨(noetherianValuationRingSelfProductExtension R K A D).1,
    ⟨(noetherianValuationRingSelfProductExtension R K A D).2⟩⟩

end Langlands.AbelianScheme
