import Langlands.AlgebraicGeometry.Deformation.AugmentedAdicCompletion
import Langlands.AlgebraicGeometry.Deformation.LocalPolynomialArtinianSource
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing

/-! # Actual complete local polynomial sources for augmented Artinian tests -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation.CompletedLocalPolynomialSource

variable {k K σ : Type u} [CommRing k] [Field K] [Algebra k K]
  [Finite σ] [IsNoetherianRing k] (ε : MvPolynomial σ k →ₐ[k] K)

/-- The actual maximal-ideal completion of the specified local polynomial source. -/
abbrev ring := AugmentedAdicCompletion.ring (R := LocalPolynomialArtinianSource.ring ε)

instance : IsNoetherianRing (ring ε) :=
  AdicCompletion.isNoetherianRing_of_isNoetherianRing _

/-- The original local polynomial source maps canonically into its completion. -/
abbrev sourceMap : LocalPolynomialArtinianSource.ring ε →ₐ[k] ring ε :=
  AugmentedAdicCompletion.sourceMap

/-- The original polynomial variables in the actual complete local source. -/
abbrev polynomialMap : MvPolynomial σ k →ₐ[k] ring ε :=
  (sourceMap ε).comp (LocalPolynomialArtinianSource.polynomialMap ε)

variable (hε : Function.Surjective ε)

/-- The specified residue augmentation on the actual completed source. -/
abbrev augmentation : ring ε →ₐ[k] K :=
  AugmentedAdicCompletion.augmentation (LocalPolynomialArtinianSource.augmentation ε)
    (LocalPolynomialArtinianSource.augmentation_surjective ε hε)

omit [Finite σ] [IsNoetherianRing k] in
lemma augmentation_surjective : Function.Surjective (augmentation ε hε) :=
  AugmentedAdicCompletion.augmentation_surjective _ _

omit [Finite σ] [IsNoetherianRing k] in
@[simp]
lemma augmentation_polynomialMap : (augmentation ε hε).comp (polynomialMap ε) = ε := by
  rw [polynomialMap, ← AlgHom.comp_assoc,
    AugmentedAdicCompletion.augmentation_sourceMap,
    LocalPolynomialArtinianSource.augmentation_polynomialMap]

/-- All maps from the actual completed source with the given residue equation. -/
abbrev Maps (A : ArtinianTest k K) :=
  AugmentedAdicCompletion.Maps (augmentation ε hε) A

/-- Restriction identifies all completed-source maps with all local-source maps. -/
def localMapEquiv (A : ArtinianTest k K) :
    Maps ε hε A ≃ LocalPolynomialArtinianSource.Maps ε A :=
  AugmentedAdicCompletion.mapEquiv (LocalPolynomialArtinianSource.augmentation ε)
    (LocalPolynomialArtinianSource.augmentation_surjective ε hε) A

/-- Completed-source maps are exactly variable coordinates with the given residues. -/
def coordinateEquiv (A : ArtinianTest k K) :
    Maps ε hε A ≃ LocalPolynomialArtinianSource.Coordinates ε A :=
  (localMapEquiv ε hε A).trans (LocalPolynomialArtinianSource.coordinateEquiv ε A)

@[simp]
lemma coordinateEquiv_apply (A : ArtinianTest k K) (α : Maps ε hε A) (i : σ) :
    (coordinateEquiv ε hε A α).val i = α.val (polynomialMap ε (MvPolynomial.X i)) := rfl

/-- Postcomposition by every actual augmented test arrow. -/
abbrev postcomp {A B : ArtinianTest k K} (q : A ⟶ B) : Maps ε hε A → Maps ε hε B :=
  AugmentedAdicCompletion.postcomp (augmentation ε hε) q

lemma localMapEquiv_naturality {A B : ArtinianTest k K} (q : A ⟶ B)
    (α : Maps ε hε A) :
    localMapEquiv ε hε B (postcomp ε hε q α) =
      LocalPolynomialArtinianSource.postcomp ε q (localMapEquiv ε hε A α) := rfl

/-- Every actual Artinian test receives a map from the same actual complete source. -/
lemma maps_nonempty (A : ArtinianTest k K) : Nonempty (Maps ε hε A) := by
  obtain ⟨α⟩ := LocalPolynomialArtinianSource.maps_nonempty ε A
  exact ⟨(localMapEquiv ε hε A).symm α⟩

/-- Every compatible completed-source map lifts across every surjective actual
augmented test arrow. -/
lemma postcomp_surjective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q)) :
    Function.Surjective (postcomp ε hε q) := by
  intro β
  obtain ⟨α, hα⟩ := LocalPolynomialArtinianSource.postcomp_surjective ε q hq
    (localMapEquiv ε hε B β)
  refine ⟨(localMapEquiv ε hε A).symm α, ?_⟩
  apply (localMapEquiv ε hε B).injective
  rw [localMapEquiv_naturality, Equiv.apply_symm_apply, hα]

section FiniteTypeResidue

variable (k K) [Algebra.FiniteType k K]

/-- One actual complete local source chosen from a finite presentation of K over k. -/
abbrev finiteTypeRing := ring (LocalPolynomialArtinianSource.finitePresentation k K).2.val

/-- The specified residue augmentation on the chosen actual complete local source. -/
abbrev finiteTypeAugmentation : finiteTypeRing k K →ₐ[k] K :=
  augmentation (LocalPolynomialArtinianSource.finitePresentation k K).2.val
    (LocalPolynomialArtinianSource.finitePresentation k K).2.property

/-- All compatible maps from the same chosen source, for every actual test. -/
abbrev FiniteTypeMaps (A : ArtinianTest k K) :=
  AugmentedAdicCompletion.Maps (finiteTypeAugmentation k K) A

/-- Every test admits a compatible map from the chosen finite-residue complete source. -/
lemma finiteType_maps_nonempty (A : ArtinianTest k K) : Nonempty (FiniteTypeMaps k K A) :=
  maps_nonempty (LocalPolynomialArtinianSource.finitePresentation k K).2.val
    (LocalPolynomialArtinianSource.finitePresentation k K).2.property A

/-- The chosen source lifts all compatible maps across all surjective test arrows. -/
lemma finiteType_postcomp_surjective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q)) :
    Function.Surjective (AugmentedAdicCompletion.postcomp (finiteTypeAugmentation k K) q) :=
  postcomp_surjective (LocalPolynomialArtinianSource.finitePresentation k K).2.val
    (LocalPolynomialArtinianSource.finitePresentation k K).2.property q hq

end FiniteTypeResidue

end Langlands.AlgebraicGeometry.Deformation.CompletedLocalPolynomialSource
