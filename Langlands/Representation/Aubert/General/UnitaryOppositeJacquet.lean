import Langlands.Representation.Aubert.General.IwahoriNaturalJacquetDuality
import Langlands.Representation.Aubert.General.UnitaryJacquetSpectrum

/-! # Opposite Jacquet nonvanishing for admissible unitary representations -/

noncomputable section

namespace Langlands.Jacquet

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U M O : Subgroup G} {g : G}

/-- An opposite contraction basis in particular supplies cofinal compact
open subgroups of the ambient group. -/
theorem compactOpenCofinal_of_oppositeIwahoriContractionBasis
    (hBasis : HasOppositeIwahoriContractionBasis U M O g) :
    CompactOpenCofinal G := by
  intro K
  obtain ⟨L, hL, hLK, -, -⟩ := hBasis K K.isOpen K.one_mem
  exact ⟨L, hL, hLK⟩

/-- Reversing the radicals and inverting the fixed element preserves the
actual opposite contraction basis. -/
theorem HasOppositeIwahoriContractionBasis.symm
    (hBasis : HasOppositeIwahoriContractionBasis U M O g) :
    HasOppositeIwahoriContractionBasis O M U g⁻¹ := by
  intro S hS h1
  obtain ⟨K, hK, hKS, hU, hO⟩ := hBasis S hS h1
  exact ⟨K, hK, hKS, hO, by simpa only [inv_inv] using hU⟩

end Langlands.Jacquet

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
  (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
  (g : G) (hc : ∀ m ∈ M, m * g = g * m)
  (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
  (hδ : ∀ m : M,
    HaarModulus.closedRestrictCharacter U hU M hMU m *
      HaarModulus.closedRestrictCharacter O hO M hMO m = 1)

/-- Compose the Hermitian identification with actual normalized opposite
Jacquet duality. The resulting conjugate-linear equivalence has source
`r_U(A)` and target the smooth dual of `r_O(A)`. -/
def unitaryOppositeJacquetDualConjugateEquiv
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (b : InvariantPositiveForm A.representation) :
    ((normalizedJacquetFunctor U M hU hMU).obj A) ≃ₗ⋆[ℂ]
      ((normalizedJacquetFunctor O M hO hMO).obj A).contragredient :=
  (unitaryJacquetConjugateEquiv U M hU hMU
    (Jacquet.compactOpenCofinal_of_oppositeIwahoriContractionBasis hBasis)
    A hA b).trans
      (SmoothRep.equivOfIso
        ((naturalNormalizedJacquetDualityOfIwahoriContractionsOfReciprocalModulus
          U M O hU hO hMU hMO g hc hBasis hδ).iso A hA)).toLinearEquiv

include hc hBasis hδ in
/-- A zero opposite normalized Jacquet module forces the original normalized
Jacquet module of an admissible unitarizable object to vanish. -/
theorem unitary_jacquet_subsingleton_of_opposite
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (hunitary : IsUnitarizable A.representation)
    (hzero : Subsingleton ((normalizedJacquetFunctor O M hO hMO).obj A)) :
    Subsingleton ((normalizedJacquetFunctor U M hU hMU).obj A) := by
  obtain ⟨b⟩ := hunitary
  have hdual :
      Subsingleton ((normalizedJacquetFunctor O M hO hMO).obj A).contragredient :=
    ⟨fun f k => by
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      rw [hzero.elim v 0]
      simp⟩
  let e := unitaryOppositeJacquetDualConjugateEquiv
    U M O hU hO hMU hMO g hc hBasis hδ A hA b
  exact ⟨fun x y => e.injective (hdual.elim _ _)⟩

include hc hBasis hδ in
/-- The two actual opposite Jacquet modules have equivalent vanishing for
every admissible unitarizable smooth object. -/
theorem unitary_jacquet_subsingleton_iff_opposite
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (hunitary : IsUnitarizable A.representation) :
    Subsingleton ((normalizedJacquetFunctor U M hU hMU).obj A) ↔
      Subsingleton ((normalizedJacquetFunctor O M hO hMO).obj A) := by
  constructor
  · apply unitary_jacquet_subsingleton_of_opposite
      O M U hO hU hMO hMU g⁻¹
      (fun m hm => Commute.inv_right (hc m hm)) hBasis.symm
      (fun m => by rw [mul_comm]; exact hδ m) A hA hunitary
  · exact unitary_jacquet_subsingleton_of_opposite
      U M O hU hO hMU hMO g hc hBasis hδ A hA hunitary

include hc hBasis hδ in
/-- Jacquet support on just one of the two opposite radicals obstructs an
invariant positive form on an admissible smooth object. -/
theorem not_isUnitarizable_of_jacquet_asymmetry
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (hnonzero : Nontrivial ((normalizedJacquetFunctor U M hU hMU).obj A))
    (hzero : Subsingleton ((normalizedJacquetFunctor O M hO hMO).obj A)) :
    ¬ IsUnitarizable A.representation := by
  intro hunitary
  exact not_subsingleton_iff_nontrivial.mpr hnonzero
    (unitary_jacquet_subsingleton_of_opposite
      U M O hU hO hMU hMO g hc hBasis hδ A hA hunitary hzero)

end Langlands.Aubert.General
