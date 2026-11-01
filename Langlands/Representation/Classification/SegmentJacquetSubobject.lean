import Langlands.Representation.Filtration.ScalarSeparatedSubobject
import Langlands.Representation.Classification.SegmentFullJacquetSplitting
import Langlands.Representation.CuspidalSupport.AssociatedProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalSubquotientProof
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Representation.Smooth.Schur.Proof

/-! Quasicuspidality and separated simple series for segment Jacquet subobjects. -/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Classification CuspidalSupport CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem subobjectJacquet_injective {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (π I : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (j : π.representation.IntertwiningMap I.representation),
      Function.Injective j → Function.Injective (T.normalizedJacquetMap B j) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π I j hj
  exact coinvariants_map_injective_of_smooth (Parabolic.unipotentFiniteContainment F T B)
    _ hj (Parabolic.isSmooth_radical F T B I.representation I.isSmooth)

private theorem supercuspidalScalarCharacter {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∃ ω : F.Carrierˣ →* ℂˣ,
      HasScalarCharacter A.obj.representation GeneralLinear.scalar ω := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
    admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
  exact ⟨χ.comp scalarToCenter, fun z v => hχ (scalarToCenter z) v⟩

/-- Every actual irreducible subrepresentation of the increasing segment
induction has a centrally separated simple series in its full cuspidal
Jacquet module. This does not identify its whole Jacquet module with one tensor. -/
theorem exists_subrepresentationJacquetSeries
    {Δ : T.Segment.{uV,uF}}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    ∃ (N : ℕ) (s : ObjectRepFiltration
        ((T.normalizedJacquetFunctor (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)).obj π).obj N)
      (c : Fin N → ℂ),
      s.HasSimpleFactors ∧ Function.Injective c ∧
        ∀ i v, (s.gradedRepresentation i).ρ
          (separatingScalar F T Δ.length Δ.rank Δ.rank_pos) v = c i • v := by
  let := T.topology
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  let I := T.segmentInduced A.obj Δ.length Δ.rank_pos
  let JI := (T.normalizedJacquetFunctor B).obj I
  let Jπ := (T.normalizedJacquetFunctor B).obj π
  obtain ⟨hπi, j, hj⟩ := (T.isSegmentSubrepresentation_iff Δ π A hA).mp hπ
  let ι : Jπ.representation.IntertwiningMap JI.representation := T.normalizedJacquetMap B j
  have hι : Function.Injective ι := subobjectJacquet_injective F T B π I j hj
  have hJπ : Jπ.HasFiniteLength :=
    (Parabolic.normalizedParabolicFiniteLength.{uF,max uF uV} F T).2 Δ.degree B π
      (SmoothRep.hasFiniteLength_of_isIrreducible hπi)
  obtain ⟨ω, hω⟩ := supercuspidalScalarCharacter F T A
  obtain ⟨N, e, s, hs, hgr, _⟩ := exists_segmentJacquetFiltration F T
    (associatedJacquetFiltration F T Δ.degree) Δ.length_pos Δ.rank_pos A ω hω
  let c : Fin N → ℂ := fun i => segmentScalar T ω Δ.rank Δ.length (blockPerm F (e i))
  have hc : Function.Injective c := fun i j h =>
    e.injective (blockPerm_injective F (segmentScalar_injective T ω Δ.rank_pos Δ.length h))
  obtain ⟨M, t, e', ht, he', htgr⟩ := SmoothRep.exists_scalarSeparatedSeries_of_injective
    JI Jπ hJπ s hs (separatingScalar F T Δ.length Δ.rank Δ.rank_pos) c hc hgr ι hι
  exact ⟨M, t, c ∘ e', ht, hc.comp he', htgr⟩

/-- The full cuspidal Jacquet module of a supplied segment subrepresentation
is quasicuspidal, by actual associated induction and hereditary exactness. -/
theorem subrepresentationJacquet_isLeviQuasicuspidal
    {Δ : T.Segment.{uV,uF}}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    IsLeviQuasicuspidal (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)
      ((T.normalizedJacquetFunctor (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)).obj π).representation := by
  let := T.topology
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  let I := T.segmentInduced A.obj Δ.length Δ.rank_pos
  let JI := (T.normalizedJacquetFunctor B).obj I
  let Jπ := (T.normalizedJacquetFunctor B).obj π
  obtain ⟨_, j, hj⟩ := (T.isSegmentSubrepresentation_iff Δ π A hA).mp hπ
  let ι : Jπ.representation.IntertwiningMap JI.representation := T.normalizedJacquetMap B j
  have hι : Function.Injective ι := subobjectJacquet_injective F T B π I j hj
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T
    Δ.length Δ.length_pos Δ.rank_pos A
  have hJI : IsLeviQuasicuspidal B JI.representation :=
    (associatedJacquetFiltration F T Δ.degree B B
      (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos))
      hσ.2.2 (LevisAssociated.refl B)).1
  apply leviQuasicuspidalSubquotient F T B JI Jπ hJI
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨Jπ, SmoothRep.ofHom ι, 𝟙 Jπ, hι, fun v => ⟨v, rfl⟩⟩

end Langlands.SegmentFullJacquet

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification SegmentFullJacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Choose an actual centrally separated simple series of the full cuspidal
Jacquet module of a supplied segment subrepresentation. -/
def IsSegmentSubrepresentation.cuspidalJacquetSeries
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    Σ N, Σ s : ObjectRepFiltration
        ((T.normalizedJacquetFunctor (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)).obj π).obj N,
      {c : Fin N → ℂ // s.HasSimpleFactors ∧ Function.Injective c ∧
        ∀ i v, (s.gradedRepresentation i).ρ
          (separatingScalar F T Δ.length Δ.rank Δ.rank_pos) v = c i • v} := by
  let := T.topology
  exact Classical.choice (by
    obtain ⟨N, s, c, hs, hc, hgr⟩ := exists_subrepresentationJacquetSeries F T π hπ A hA
    exact ⟨⟨N, s, c, hs, hc, hgr⟩⟩)

end Langlands.PadicField.TopologicalData
