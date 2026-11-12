import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianNormedExtensionEmbedding
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionPointEmbeddingStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective

/-! # Open-subspace reductions for henselian extension point maps -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace ExtensionLocalReduction

/-- Local finite type passes to an open subspace. -/
theorem locallyOfFiniteType_of_open {S : Scheme.{u}} {U X : AlgebraicSpace S}
    (hX : LocallyOfFiniteTypeOverBase X) (j : U ⟶ X)
    (hj : IsOpenImmersion (hom j)) : LocallyOfFiniteTypeOverBase U := by
  obtain ⟨V, a, ha, hs, hV⟩ := hX
  let W := hj.rep.pullback a
  let b := hj.rep.fst a
  let p := hj.rep.snd a
  have hp : _root_.AlgebraicGeometry.IsOpenImmersion p.left := hj.property_snd a
  have hW : LocallyOfFiniteType W.hom := by
    rw [← Over.w p]
    infer_instance
  have hb : IsEtale b := by
    let : MorphismProperty.IsStableUnderBaseChange (@IsEtale S) :=
      MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
        (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback (hj.rep.isPullback a).flip ha
  have hb' : IsSurjective b := by
    let : MorphismProperty.IsStableUnderBaseChange (@IsSurjective S) :=
      MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
        (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback (hj.rep.isPullback a).flip hs
  exact ⟨W, b, hb, hb', hW⟩

/-- Membership in the image of an open subspace descends under field extension. -/
theorem mem_range_of_changeRing_mem_range
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {U X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (j : U ⟶ X) (hj : IsOpenImmersion (hom j)) (x : RingPoints K X K)
    (hx : RingPoints.changeRing (Algebra.ofId K L) x ∈
      Set.range (RingPoints.map (A := L) j)) :
    x ∈ Set.range (RingPoints.map (A := K) j) := by
  let A := Subfunctor.range (hom j)
  have hA : IsOpenImmersion A.ι := by
    let : Mono (hom j) := SliceOpenGluing.relative_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone SliceOpenGluing.openProperty_le_monomorphisms _ hj)
    let : (@OpenSubfunctorLifting.openMorphism (Spec (CommRingCat.of K))).RespectsIso := by
      change ((SliceOpenGluing.openProperty _).relative (schemeYoneda _)).RespectsIso
      infer_instance
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@OpenSubfunctorLifting.openMorphism (Spec (CommRingCat.of K)))
      (Subfunctor.toRange (hom j)) A.ι).mp
    change IsOpenImmersion (hom j)
    exact hj
  have : Surjective (ringTestMap K (Algebra.ofId K L)).left := by
    change Surjective (Spec.algebraMap K L)
    infer_instance
  exact OpenSubfunctorPoints.mem_of_surjective hA
    (ringTestMap K (Algebra.ofId K L)) x hx

/-- Coefficient extension is natural in the space. -/
theorem extensionPointMap_natural
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] {U X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (j : U ⟶ X) (x : RingPoints K U K) :
    extensionPointMap L X (RingPoints.map j x) =
      RingPoints.map (baseChangeMap (Spec.algebraMap K L) j) (extensionPointMap L U x) := by
  apply (baseChangeRingPointsEquiv K L L X).injective
  rw [extensionPointMap, Equiv.apply_symm_apply, baseChangeRingPointsEquiv_map,
    extensionPointMap, Equiv.apply_symm_apply, RingPoints.changeRing_map]

/-- The square of point maps for an open subspace has the expected inverse image of ranges. -/
theorem preimage_range_baseChangeMap
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] {U X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (j : U ⟶ X) (hj : IsOpenImmersion (hom j)) :
    extensionPointMap L X ⁻¹'
        Set.range (RingPoints.map (A := L) (baseChangeMap (Spec.algebraMap K L) j)) =
      Set.range (RingPoints.map (A := K) j) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    apply mem_range_of_changeRing_mem_range j hj x (L := L)
    refine ⟨baseChangeRingPointsEquiv K L L U y, ?_⟩
    have h := congrArg (baseChangeRingPointsEquiv K L L X) hy
    rw [baseChangeRingPointsEquiv_map, extensionPointMap, Equiv.apply_symm_apply] at h
    exact h
  · rintro ⟨y, rfl⟩
    exact ⟨extensionPointMap L U y, (extensionPointMap_natural j y).symm⟩

section Henselian

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L] (hK : IsHenselianValuedField K) (hL : IsHenselianValuedField L)
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}
variable (hX : IsQuasiSeparatedLocallyFiniteType K X)

include hX

/-- A separated open subspace inherits the hypotheses required for the chart topology. -/
theorem separated_open_properties
    {U : AlgebraicSpace (Spec (CommRingCat.of K))} (j : U ⟶ X)
    (hj : IsOpenImmersion (hom j)) (hs : IsSeparated U) :
    IsQuasiSeparatedLocallyFiniteType K U :=
  ⟨SpaceProductPoints.isQuasiSeparated_of_isSeparated hs, locallyOfFiniteType_of_open hX.2 j hj⟩

include hL in
/-- The inverse image in a separated open subspace of the extended rational locus is
exactly its own extended rational locus. -/
theorem preimage_range_extensionPointMap
    {U : AlgebraicSpace (Spec (CommRingCat.of K))} (j : U ⟶ X)
    (hj : IsOpenImmersion (hom j)) (hs : IsSeparated U) :
    RingPoints.map (A := L) (baseChangeMap (Spec.algebraMap K L) j) ⁻¹'
        Set.range (extensionPointMap L X) = Set.range (extensionPointMap L U) := by
  have hU := separated_open_properties hX j hj hs
  have hXL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) X) :=
    ⟨hX.1.baseChange, hX.2.baseChange⟩
  have hUL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) U) :=
    ⟨hU.1.baseChange, hU.2.baseChange⟩
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) U) L) :=
    etaleChartTopology L _
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  have hinj := (isOpenEmbedding_ringPointsMap hL hUL hXL _ hj.baseChangeMap).injective
  ext z
  constructor
  · rintro ⟨y, hy⟩
    have hyU : y ∈ Set.range (RingPoints.map (A := K) j) := by
      rw [← preimage_range_baseChangeMap (L := L) j hj]
      exact ⟨z, hy.symm⟩
    obtain ⟨v, rfl⟩ := hyU
    refine ⟨v, hinj ?_⟩
    exact (extensionPointMap_natural j v).symm.trans hy
  · rintro ⟨v, rfl⟩
    exact ⟨RingPoints.map j v, extensionPointMap_natural j v⟩

include hK hL in
/-- The separated embedding theorem glues over the separated open covering. -/
theorem isEmbedding_of_covered
    (hcov : IsCoveredBySeparatedOpenSubspaces K X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (extensionPointMap L X) := by
  classical
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  let f := extensionPointMap L X
  have hXL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) X) :=
    ⟨hX.1.baseChange, hX.2.baseChange⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨U, j, hj, hs, u, hu⟩ := hcov K x
    have hU := separated_open_properties hX j hj hs
    let : TopologicalSpace (RingPoints K U K) := etaleChartTopology K U
    let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) U) L) :=
      etaleChartTopology L _
    have hUL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) U) :=
      ⟨hU.1.baseChange, hU.2.baseChange⟩
    have hjL := isOpenEmbedding_ringPointsMap hL hUL hXL _ hj.baseChangeMap
    have hfU := isEmbedding_henselianExtensionPointMap hK hL hU hs
    have hyU : y ∈ Set.range (RingPoints.map (A := K) j) := by
      rw [← preimage_range_baseChangeMap (L := L) j hj]
      refine ⟨extensionPointMap L U u, ?_⟩
      rw [← extensionPointMap_natural, hu]
      exact hxy
    obtain ⟨v, hv⟩ := hyU
    have huv : u = v := hfU.injective (hjL.injective (by
      rw [← extensionPointMap_natural, ← extensionPointMap_natural, hu, hv]
      exact hxy))
    exact hu.symm.trans ((congrArg (RingPoints.map j) huv).trans hv)
  have hcont : Continuous f := continuous_extensionPointMap L
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hlocal : ∀ x : W, ∃ N : Set (RingPoints L (baseChange (Spec.algebraMap K L) X) L),
      IsOpen N ∧ f x ∈ N ∧ f ⁻¹' N ⊆ W := by
    intro x
    obtain ⟨U, j, hj, hs, u, hu⟩ := hcov K x
    have hU := separated_open_properties hX j hj hs
    let : TopologicalSpace (RingPoints K U K) := etaleChartTopology K U
    let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) U) L) :=
      etaleChartTopology L _
    have hUL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) U) :=
      ⟨hU.1.baseChange, hU.2.baseChange⟩
    let jK := RingPoints.map (A := K) j
    let jL := RingPoints.map (A := L) (baseChangeMap (Spec.algebraMap K L) j)
    have hjK := isOpenEmbedding_ringPointsMap hK hU hX j hj
    have hjL := isOpenEmbedding_ringPointsMap hL hUL hXL _ hj.baseChangeMap
    have hfU := isEmbedding_henselianExtensionPointMap hK hL hU hs
    obtain ⟨V, hVo, hVe⟩ := hfU.isInducing.isOpen_iff.mp (hW.preimage hjK.continuous)
    refine ⟨jL '' V, hjL.isOpenMap _ hVo, ?_, ?_⟩
    · refine ⟨extensionPointMap L U u, ?_, ?_⟩
      · change u ∈ extensionPointMap L U ⁻¹' V
        rw [hVe]
        change RingPoints.map j u ∈ W
        rw [hu]
        exact x.property
      · exact (extensionPointMap_natural j u).symm.trans (congrArg f hu)
    · intro y hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hyU : y ∈ Set.range jK := by
        rw [← preimage_range_baseChangeMap (L := L) j hj]
        exact ⟨z, hzy⟩
      obtain ⟨v, hv⟩ := hyU
      change RingPoints.map j v = y at hv
      have hev : extensionPointMap L U v = z := hjL.injective (by
        rw [← extensionPointMap_natural, hv]
        exact hzy.symm)
      have hvW : v ∈ jK ⁻¹' W := by
        rw [← hVe]
        change extensionPointMap L U v ∈ V
        rwa [hev]
      exact hv ▸ hvW
  choose N hNo hNx hNsub using hlocal
  refine isOpen_induced_iff.mpr ⟨⋃ x : W, N x, isOpen_iUnion hNo, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx⟩
    exact hNsub x hx
  · intro hy
    exact ⟨⟨y, hy⟩, hNx ⟨y, hy⟩⟩

include hL in
/-- Closedness of the extension locus can be checked on separated open subspaces. -/
theorem isClosed_range_of_separated_open
    (hcov : IsCoveredBySeparatedOpenSubspaces K X)
    (hclosed : ∀ (U : AlgebraicSpace (Spec (CommRingCat.of K)))
      (j : U ⟶ X), IsOpenImmersion (hom j) → IsSeparated U →
        IsClosed[etaleChartTopology L (baseChange (Spec.algebraMap K L) U)]
          (Set.range (extensionPointMap L U))) :
    IsClosed[etaleChartTopology L (baseChange (Spec.algebraMap K L) X)]
      (Set.range (extensionPointMap L X)) := by
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨U, j, hj, hs, u, hu⟩ := hcov L (baseChangeRingPointsEquiv K L L X z)
  have hU := separated_open_properties hX j hj hs
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) U) L) :=
    etaleChartTopology L _
  have hXL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) X) :=
    ⟨hX.1.baseChange, hX.2.baseChange⟩
  have hUL : IsQuasiSeparatedLocallyFiniteType L (baseChange (Spec.algebraMap K L) U) :=
    ⟨hU.1.baseChange, hU.2.baseChange⟩
  let jL := RingPoints.map (A := L) (baseChangeMap (Spec.algebraMap K L) j)
  have hjL := isOpenEmbedding_ringPointsMap hL hUL hXL _ hj.baseChangeMap
  have hu' : jL ((baseChangeRingPointsEquiv K L L U).symm u) = z := by
    apply (baseChangeRingPointsEquiv K L L X).injective
    rw [baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]
    exact hu
  have hpre := preimage_range_extensionPointMap hL hX j hj hs
  refine ⟨jL '' (Set.range (extensionPointMap L U))ᶜ, ?_,
    hjL.isOpenMap _ (hclosed U j hj hs).isOpen_compl, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ hmem
    apply hv
    rw [← hpre]
    exact hmem
  · refine ⟨(baseChangeRingPointsEquiv K L L U).symm u, ?_, hu'⟩
    intro hv
    apply hz
    rw [← hu']
    change (baseChangeRingPointsEquiv K L L U).symm u ∈
      jL ⁻¹' Set.range (extensionPointMap L X)
    rw [hpre]
    exact hv

end Henselian

/-- The canonical homeomorphism onto the image under the full separated-open covering
hypothesis of Conrad's Proposition 5.11(3). -/
def coveredHenselianExtensionPointHomeomorphRange
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] (hK : IsHenselianValuedField K) (hL : IsHenselianValuedField L)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (hcov : IsCoveredBySeparatedOpenSubspaces K X) :
    letI : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
    letI : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
      etaleChartTopology L _
    RingPoints K X K ≃ₜ Set.range (extensionPointMap L X) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  exact (isEmbedding_of_covered hK hL hX hcov).toHomeomorph

end ExtensionLocalReduction
end Langlands.AlgebraicGeometry.AlgebraicSpace
