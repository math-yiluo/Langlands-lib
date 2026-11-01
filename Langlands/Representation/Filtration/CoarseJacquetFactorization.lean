import Langlands.Representation.Filtration.CoarseJacquetExtraction
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Smooth.Admissibility.ExactProof
import Langlands.Group.GL.CompactOpen

/-! Admissible actual coarse constituents and their same-universe tensor
factorizations, retaining every outside block. -/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual smooth subquotients inherit admissibility when compact open
subgroups are cofinal among open subgroups. -/
theorem isAdmissible_of_subquotient_of_compactOpenCofinal
    (hcofinal : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.IsAdmissible) (hD : IsSubquotient D A) : D.IsAdmissible := by
  obtain ⟨X, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hD
  have hX : X.IsAdmissible := isAdmissible_of_injective (hom i) hi hA
  exact ((isAdmissible_iff_of_shortExact hcofinal
    (hom (kernelι q)) (hom q) (subtype_injective _ _) hq
    (Submodule.range_subtype _) X.isSmooth).mp hX).2

end Langlands.SmoothRep

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem levi_compactOpen_cofinal :
    letI := T.topology
    ∀ H : OpenSubgroup (B.Levi F.Carrier),
      ∃ K : OpenSubgroup (B.Levi F.Carrier),
        IsCompact (K : Set (B.Levi F.Carrier)) ∧ K ≤ H := by
  let := T.topology
  intro H
  obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen B H
    (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, fun x hx => hKH hx⟩

private theorem finiteLength_of_irreducible
    {G : Type uF} [Group G] [TopologicalSpace G]
    {A : SmoothRep.{0, uF, uV} ℂ G}
    (hA : A.IsIrreducible) : A.HasFiniteLength := by
  have : IsSimpleModule (MonoidAlgebra ℂ G) A.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩

/-- Extract an admissible finite-length actual irreducible constituent of the
whole coarse Jacquet module, with the given refined occurrence. -/
theorem exists_admissible_irreducible_coarseJacquet_subquotient :
    letI := T.topology
    ∀ {π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      {D : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S)},
      π.IsAdmissible → π.HasFiniteLength → D.IsIrreducible →
      SmoothRep.IsSubquotient D ((T.normalizedComposedJacquetFunctor B S).obj π) →
      ∃ E : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        E.IsIrreducible ∧ E.IsAdmissible ∧ E.HasFiniteLength ∧
        SmoothRep.IsSubquotient E ((T.normalizedJacquetFunctor B).obj π) ∧
        SmoothRep.IsSubquotient D ((T.normalizedRefinedJacquetFunctor B S).obj E) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro π D hπ hfin hD h
  obtain ⟨E, hEi, hE, hDE⟩ :=
    exists_irreducible_coarseJacquet_subquotient T B S hπ hfin hD h
  refine ⟨E, hEi, ?_, finiteLength_of_irreducible hEi, hE, hDE⟩
  exact SmoothRep.isAdmissible_of_subquotient_of_compactOpenCofinal
    (levi_compactOpen_cofinal T B)
    (A := (T.normalizedJacquetFunctor B).obj π) (D := E)
    (FiniteLengthAssembly.isAdmissible_normalizedJacquet T B π.representation hπ) hE

/-- A family of actual admissible finite-length irreducible block factors whose
external tensor occurs in the coarse Jacquet module and retains `D` after
refinement. Both occurrences use the existing actual subquotient relation. -/
def IsCoarseJacquetFactorization :
    letI := T.topology
    (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) →
    (D : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S)) →
    (A : ∀ i : Fin B.length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) → Prop := by
  let := T.topology
  intro π D A
  exact (∀ i, (A i).IsIrreducible) ∧
    (∀ i, (A i).IsAdmissible) ∧
    (∀ i, (A i).HasFiniteLength) ∧
    SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject A)
      ((T.normalizedJacquetFunctor B).obj π) ∧
    SmoothRep.IsSubquotient D
      ((T.normalizedRefinedJacquetFunctor B S).obj
        (FiniteTensor.externalSmoothObject A))

/-- An extracted coarse constituent may be realized as an actual external
tensor of admissible finite-length irreducible block representations. Both
actual occurrences are retained, over the entire coarse Levi. -/
theorem exists_factorized_coarseJacquet_subquotient (hn : 0 < n) :
    letI := T.topology
    ∀ {π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
      {D : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S)},
      π.IsAdmissible → π.HasFiniteLength → D.IsIrreducible →
      SmoothRep.IsSubquotient D ((T.normalizedComposedJacquetFunctor B S).obj π) →
      ∃ A : ∀ i : Fin B.length,
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
        IsCoarseJacquetFactorization T B S π D A := by
  let := T.topology
  intro π D hπ hfin hD h
  obtain ⟨E, hEi, hEa, _, hE, hDE⟩ :=
    exists_admissible_irreducible_coarseJacquet_subquotient T B S hπ hfin hD h
  obtain ⟨A, hAi, hAa, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization p F T n hn B E hEi hEa
  let e' : E ≅ FiniteTensor.externalSmoothObject A := SmoothRep.mkIso e
  exact ⟨A, hAi, hAa, fun i => finiteLength_of_irreducible (hAi i),
    hE.of_iso_left e',
    hDE.of_iso_right ((T.normalizedRefinedJacquetFunctor B S).mapIso e')⟩

end Langlands.Parabolic
