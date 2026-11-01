import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.ExactConstituentExtraction
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof

/-! Actual extraction from an arbitrary refinement of a coarse upper Jacquet
module. The coarse object is retained, including every outside block. -/

noncomputable section

open CategoryTheory



namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

theorem normalizedRefinedJacquet_mapsShortExact :
    letI := T.topology
    Derivative.Mirabolic.MapsShortExactIntertwiners
      (T.normalizedRefinedJacquetFunctor.{uF, uV} B S) := by
  let := T.topology
  intro A C D i q hi hq hex
  exact CuspidalSupport.RefinedJacquetLengthProof.map_exact T B S
    (SmoothRep.hom i) (SmoothRep.hom q) C.isSmooth hi hq hex

instance normalizedRefinedJacquet_preservesZeroMorphisms :
    letI := T.topology
    (T.normalizedRefinedJacquetFunctor.{uF, uV} B S).PreservesZeroMorphisms := by
  let := T.topology
  constructor
  intro A C
  ext x
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective A.representation
    (refinedUnipotent F.Carrier B S) x
  change refinedJacquetMk B S C.representation (0 : C) = 0
  exact map_zero _

/-- Refine every step of an actual object filtration by its mapped invariant
image. All coarse blocks and every supplied step are retained. -/
def refinedJacquetImageFiltration :
    letI := T.topology
    ∀ {A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)} {r : ℕ},
      ObjectRepFiltration A.obj r →
        ObjectRepFiltration
          ((T.normalizedRefinedJacquetFunctor B S).obj A).obj r := by
  letI := T.topology
  intro A r s
  exact s.exactSmoothImage (T.normalizedRefinedJacquetFunctor B S)

/-- The objectwise normalized transitivity comparison for this refinement. -/
def iteratedCoarseJacquetIso :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      (T.normalizedRefinedJacquetFunctor B S).obj
          ((T.normalizedJacquetFunctor B).obj π) ≅
        (T.normalizedComposedJacquetFunctor B S).obj π := by
  letI := T.topology
  intro π
  exact (Classical.choose
    (normalizedRefinementJacquetTransitivity.{uF, uV} F T B S)).app π

/-- A finite-length admissible ambient object has a finite-length actual coarse
Jacquet module. The ambient object need not be irreducible. -/
theorem coarseJacquet_hasFiniteLength :
    letI := T.topology
    ∀ {π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)},
      π.IsAdmissible → π.HasFiniteLength →
        ((T.normalizedJacquetFunctor B).obj π).HasFiniteLength := by
  let := T.topology
  intro π hπ hfin
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  exact normalizedJacquetFiniteLength T B π.representation hπ inferInstance

/-- Extract an actual irreducible constituent of the entire coarse Levi object
from an irreducible occurrence in its composed upper Jacquet module. -/
theorem exists_irreducible_coarseJacquet_subquotient :
    letI := T.topology
    ∀ {π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      {D : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S)},
      π.IsAdmissible → π.HasFiniteLength → D.IsIrreducible →
      SmoothRep.IsSubquotient D ((T.normalizedComposedJacquetFunctor B S).obj π) →
      ∃ E : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        E.IsIrreducible ∧
        SmoothRep.IsSubquotient E ((T.normalizedJacquetFunctor B).obj π) ∧
        SmoothRep.IsSubquotient D ((T.normalizedRefinedJacquetFunctor B S).obj E) := by
  let := T.topology
  intro π D hπ hfin hD h
  exact ObjectRepFiltration.exists_irreducible_subquotient_of_image
    (coarseJacquet_hasFiniteLength T B hπ hfin)
    (T.normalizedRefinedJacquetFunctor B S)
    (normalizedRefinedJacquet_mapsShortExact T B S) hD
    (h.of_iso_right (iteratedCoarseJacquetIso T B S π).symm)

/-- Any actual occurrence after refining an extracted coarse constituent
returns to the corresponding composed Jacquet module of the same ambient
object. There are no restrictions on the other coarse blocks. -/
theorem subquotient_composedJacquet_of_coarse_subquotient :
    letI := T.topology
    ∀ {π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      {E : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)}
      {D : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S)},
      SmoothRep.IsSubquotient E ((T.normalizedJacquetFunctor B).obj π) →
      SmoothRep.IsSubquotient D ((T.normalizedRefinedJacquetFunctor B S).obj E) →
      SmoothRep.IsSubquotient D ((T.normalizedComposedJacquetFunctor B S).obj π) := by
  let := T.topology
  intro π E D hE hD
  exact (smoothSubquotientTransitivity ℂ _ _ _ _ hD
    (ExactSmoothTransport.map_isSubquotient
    (T.normalizedRefinedJacquetFunctor B S)
    (normalizedRefinedJacquet_mapsShortExact T B S) hE)).of_iso_right
      (iteratedCoarseJacquetIso T B S π)

end Langlands.Parabolic
