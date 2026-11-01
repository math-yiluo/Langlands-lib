import Langlands.Geometry.Analytic.DirectedRationalAtlas
import Langlands.Geometry.Analytic.DirectedAtlasDomainLocalization
import Langlands.Geometry.Analytic.AtlasReindexing
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Full strong comparison with every local rational locus -/

noncomputable section

universe u v w

namespace Langlands.Analytic.DirectedRationalAtlas

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open IndexedAffinoidAtlas.DirectedDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (hd : a.HasDirectedCharts)

/-- Relative full representation for any directed-domain arrow whose ambient
containing map is injective. The closedness follows from its compact spectrum. -/
theorem inclusion_represents {U V : IndexedAffinoidAtlas.DirectedDomain a hd}
    (f : U ⟶ V) (hinj : Function.Injective V.ambientMap) :
    Represents K f.restriction (V.ambientMap ⁻¹' U.locus) := by
  have hrange : Set.range f.spectrumMap = V.ambientMap ⁻¹' U.locus := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change V.ambientMap (f.spectrumMap y) ∈ U.locus
      rw [f.ambientMap_naturality, ← U.range_ambientMap]
      exact Set.mem_range_self y
    · intro hx
      obtain ⟨y, hy⟩ := U.range_ambientMap.symm ▸ hx
      exact ⟨y, hinj ((f.ambientMap_naturality y).trans hy)⟩
  refine ⟨?_, hrange, ?_⟩
  · rw [← hrange]
    exact (isCompact_range f.spectrumMap.continuous).isClosed
  · intro R φ hφ
    exact inclusion_universal a hd f R φ hφ

@[simp]
theorem originalChart_ambientMap (i : a.Index) (x : BanachSpectrum (a.algebra i)) :
    (originalChart a hd i).ambientMap x = a.chart i x := by
  change a.chart i (BanachSpectrum.comap (BoundedRingHom.id (a.algebra i)) x) = _
  rw [BanachSpectrum.comap_id]

/-- Every original bounded restriction is an actual arrow of the common
represented-domain category. -/
def originalInclusion (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    originalChart a hd i ⟶ originalChart a hd j where
  subset := by simpa only [originalChart_locus] using h
  restriction := a.restriction i j h
  comp_baseMap q hiq hjq := by
    change Set.range (a.chart i) ⊆ Set.range (a.chart q) at hiq
    change Set.range (a.chart j) ⊆ Set.range (a.chart q) at hjq
    change (a.restriction i j h).comp
      ((BoundedAlgHom.id K (a.algebra j)).comp (a.restriction j q hjq)) =
      (BoundedAlgHom.id K (a.algebra i)).comp (a.restriction i q hiq)
    rw [BoundedAlgHom.id_comp, BoundedAlgHom.id_comp]
    exact (a.restriction_comp i j q h hjq hiq).symm

/-- Each admissible original-to-rational pair receives its actual bounded
restriction from the common represented-domain category. -/
def fromOriginalInclusion (i : a.Index) (s : Index a)
    (h : Set.range (a.chart i) ⊆ Set.range (chart a s)) :
    originalChart a hd i ⟶ s.directedDomain a hd :=
  Inclusion.ofSubset _ _ (by
    simpa only [originalChart_locus, Index.directedDomain_locus, range_chart] using h)

/-- Each admissible rational-to-original pair retains the full bounded map. -/
def toOriginalInclusion (s : Index a) (i : a.Index)
    (h : Set.range (chart a s) ⊆ Set.range (a.chart i)) :
    s.directedDomain a hd ⟶ originalChart a hd i :=
  Inclusion.ofSubset _ _ (by
    simpa only [originalChart_locus, Index.directedDomain_locus, range_chart] using h)

theorem fromOriginalInclusion_naturality (i i' : a.Index) (s s' : Index a)
    (hi : Set.range (a.chart i) ⊆ Set.range (a.chart i'))
    (hs : Set.range (chart a s) ⊆ Set.range (chart a s'))
    (h : Set.range (a.chart i) ⊆ Set.range (chart a s))
    (h' : Set.range (a.chart i') ⊆ Set.range (chart a s')) :
    (a.restriction i i' hi).comp (fromOriginalInclusion a hd i' s' h').restriction =
      (fromOriginalInclusion a hd i s h).restriction.comp (restriction a hd s s' hs) :=
  congrArg Inclusion.restriction
    (@Subsingleton.elim (Inclusion (originalChart a hd i) (s'.directedDomain a hd))
      inferInstance
      (originalInclusion a hd i i' hi ≫ fromOriginalInclusion a hd i' s' h')
      (fromOriginalInclusion a hd i s h ≫ inclusion a hd s s' hs))

theorem toOriginalInclusion_naturality (s s' : Index a) (i i' : a.Index)
    (hs : Set.range (chart a s) ⊆ Set.range (chart a s'))
    (hi : Set.range (a.chart i) ⊆ Set.range (a.chart i'))
    (h : Set.range (chart a s) ⊆ Set.range (a.chart i))
    (h' : Set.range (chart a s') ⊆ Set.range (a.chart i')) :
    (restriction a hd s s' hs).comp (toOriginalInclusion a hd s' i' h').restriction =
      (toOriginalInclusion a hd s i h).restriction.comp (a.restriction i i' hi) :=
  congrArg Inclusion.restriction
    (@Subsingleton.elim (Inclusion (s.directedDomain a hd) (originalChart a hd i'))
      inferInstance
      (inclusion a hd s s' hs ≫ toOriginalInclusion a hd s' i' h')
      (toOriginalInclusion a hd s i h ≫ originalInclusion a hd i i' hi))

/-- Reindexing changes only the original index names and their universe. -/
def originalPresentation : AffinoidAtlasPresentation.{u, v, max v w} K where
  space := TopCat.of X
  atlas := a.reindex (Equiv.ulift : ULift.{v} a.Index ≃ a.Index)

/-- The rational presentation has the same index universe as the original. -/
def presentation : AffinoidAtlasPresentation.{u, v, max v w} K where
  space := TopCat.of X
  atlas := (atlas a hd).reindex (Equiv.ulift : ULift.{w} (Index a) ≃ Index a)

/-- Every admissible pair uses the actual directed-domain inclusion. -/
def fromOriginal : StrongHom (originalPresentation a) (presentation a hd) where
  baseMap := ContinuousMap.id X
  target_exists i := ⟨⟨Index.ofOriginal a i.down⟩, by
    change _root_.id '' Set.range (a.chart i.down) ⊆
      Set.range ((atlas a hd).chart (Index.ofOriginal a i.down))
    rw [Set.image_id, atlas_ofOriginal_range]⟩
  pullback i s h :=
    (fromOriginalInclusion a hd i.down s.down (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm i s h x := by
    change ULift.{v} a.Index at i
    change ULift.{w} (Index a) at s
    change _root_.id '' Set.range (a.chart i.down) ⊆ Set.range (chart a s.down) at h
    change BanachSpectrum (a.algebra i.down) at x
    have he := (fromOriginalInclusion a hd i.down s.down
      (fun x hx => h ⟨x, hx, rfl⟩)).ambientMap_naturality x
    change chart a s.down (BanachSpectrum.comap
      (fromOriginalInclusion a hd i.down s.down
        (fun x hx => h ⟨x, hx, rfl⟩)).restriction.toBoundedRingHom x) = a.chart i.down x
    change chart a s.down (BanachSpectrum.comap
      (fromOriginalInclusion a hd i.down s.down
        (fun x hx => h ⟨x, hx, rfl⟩)).restriction.toBoundedRingHom x) =
      (originalChart a hd i.down).ambientMap x at he
    rw [originalChart_ambientMap] at he
    exact he
  restriction_comm i i' s s' hi hs h h' :=
    fromOriginalInclusion_naturality a hd i.down i'.down s.down s'.down hi hs
      (fun x hx => h ⟨x, hx, rfl⟩) (fun x hx => h' ⟨x, hx, rfl⟩)

/-- A rational locus has its chosen original chart as a containing target. -/
def toOriginal : StrongHom (presentation a hd) (originalPresentation a) where
  baseMap := ContinuousMap.id X
  target_exists s := ⟨⟨s.down.original a⟩, by
    change _root_.id '' Set.range (chart a s.down) ⊆
      Set.range (a.chart (s.down.original a))
    rw [Set.image_id, range_chart, ← s.down.locus_original_rational a]
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩⟩
  pullback s i h :=
    (toOriginalInclusion a hd s.down i.down (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm s i h x := by
    change ULift.{w} (Index a) at s
    change ULift.{v} a.Index at i
    change _root_.id '' Set.range (chart a s.down) ⊆ Set.range (a.chart i.down) at h
    change BanachSpectrum (s.down.rational a).algebra at x
    have he := (toOriginalInclusion a hd s.down i.down
      (fun x hx => h ⟨x, hx, rfl⟩)).ambientMap_naturality x
    change a.chart i.down (BanachSpectrum.comap
      (toOriginalInclusion a hd s.down i.down
        (fun x hx => h ⟨x, hx, rfl⟩)).restriction.toBoundedRingHom x) = chart a s.down x
    change (originalChart a hd i.down).ambientMap (BanachSpectrum.comap
      (toOriginalInclusion a hd s.down i.down
        (fun x hx => h ⟨x, hx, rfl⟩)).restriction.toBoundedRingHom x) = chart a s.down x at he
    exact (originalChart_ambientMap a hd i.down _).symm.trans he
  restriction_comm s s' i i' hs hi h h' :=
    toOriginalInclusion_naturality a hd s.down s'.down i.down i'.down hs hi
      (fun x hx => h ⟨x, hx, rfl⟩) (fun x hx => h' ⟨x, hx, rfl⟩)

@[simp]
theorem fromOriginal_baseMap : (fromOriginal a hd).baseMap = ContinuousMap.id X := rfl

@[simp]
theorem toOriginal_baseMap : (toOriginal a hd).baseMap = ContinuousMap.id X := rfl

/-- Full factorization proves the forward comparison at every admissible pair. -/
theorem isQuasiIso_fromOriginal : (fromOriginal a hd).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i s h
  change ULift.{v} a.Index at i
  change ULift.{w} (Index a) at s
  change _root_.id '' Set.range (a.chart i.down) ⊆ Set.range (chart a s.down) at h
  change Represents K (fromOriginalInclusion a hd i.down s.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
    (chart a s.down ⁻¹' (_root_.id '' Set.range (a.chart i.down)))
  rw [Set.image_id]
  have hp := inclusion_represents a hd (fromOriginalInclusion a hd i.down s.down
    (fun x hx => h ⟨x, hx, rfl⟩)) (isEmbedding_chart a s.down).injective
  simp only [originalChart_locus] at hp
  change Represents K (fromOriginalInclusion a hd i.down s.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
    (chart a s.down ⁻¹' Set.range (a.chart i.down)) at hp
  exact hp

/-- Full representation also holds for the entire reverse comparison. -/
theorem isQuasiIso_toOriginal : (toOriginal a hd).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro s i h
  change ULift.{w} (Index a) at s
  change ULift.{v} a.Index at i
  change Represents K (toOriginalInclusion a hd s.down i.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
    (a.chart i.down ⁻¹' (_root_.id '' Set.range (chart a s.down)))
  rw [Set.image_id]
  simpa only [Index.directedDomain_locus, range_chart] using
    represents_toOriginalChart a hd i.down (s.down.directedDomain a hd)
      (toOriginalInclusion a hd s.down i.down (fun x hx => h ⟨x, hx, rfl⟩))

/-- The whole rational locus and the original chart have the same ambient set,
although their chosen quotient algebras need not be definitionally equal. -/
theorem original_locus_eq (i : a.Index) :
    (originalChart a hd i).locus = ((Index.ofOriginal a i).directedDomain a hd).locus := by
  rw [originalChart_locus, Index.directedDomain_locus, Index.val_ofOriginal]

/-- The actual bounded equivalence between an original algebra and the chosen
rational quotient representing its whole spectrum. -/
def originalAlgebraEquiv (i : a.Index) :
    BoundedAlgEquiv K (a.algebra i) ((Index.ofOriginal a i).rational a).algebra :=
  boundedEquivOfLocusEq (originalChart a hd i)
    ((Index.ofOriginal a i).directedDomain a hd) (original_locus_eq a hd i)

theorem originalAlgebraEquiv_toBoundedAlgHom (i : a.Index)
    (h : Set.range (chart a (Index.ofOriginal a i)) ⊆ Set.range (a.chart i)) :
    (originalAlgebraEquiv a hd i).toBoundedAlgHom =
      (toOriginalInclusion a hd (Index.ofOriginal a i) i h).restriction := by
  ext b
  change (isoOfLocusEq (originalChart a hd i) ((Index.ofOriginal a i).directedDomain a hd)
    (original_locus_eq a hd i)).inv.restriction b = _
  exact congrArg
    (fun f : Inclusion ((Index.ofOriginal a i).directedDomain a hd) (originalChart a hd i) =>
      f.restriction b) (Subsingleton.elim _ _)

theorem originalAlgebraEquiv_symm_toBoundedAlgHom (i : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (chart a (Index.ofOriginal a i))) :
    (originalAlgebraEquiv a hd i).symm.toBoundedAlgHom =
      (fromOriginalInclusion a hd i (Index.ofOriginal a i) h).restriction := by
  ext b
  change (isoOfLocusEq (originalChart a hd i) ((Index.ofOriginal a i).directedDomain a hd)
    (original_locus_eq a hd i)).hom.restriction b = _
  exact congrArg
    (fun f : Inclusion (originalChart a hd i) ((Index.ofOriginal a i).directedDomain a hd) =>
      f.restriction b) (Subsingleton.elim _ _)

/-- On the retained whole original locus, the forward pullback is exactly the
inverse of the constructed bounded algebra equivalence. -/
theorem fromOriginal_pullback_ofOriginal (i : a.Index)
    (h : _root_.id '' Set.range (a.chart i) ⊆ Set.range (chart a (Index.ofOriginal a i))) :
    (fromOriginal a hd).pullback
        (ULift.up i : (originalPresentation a).atlas.Index)
        (ULift.up (Index.ofOriginal a i) : (presentation a hd).atlas.Index) h =
      (originalAlgebraEquiv a hd i).symm.toBoundedAlgHom :=
  (originalAlgebraEquiv_symm_toBoundedAlgHom a hd i (fun x hx => h ⟨x, hx, rfl⟩)).symm

/-- The reverse pullback on that locus is the forward bounded equivalence. -/
theorem toOriginal_pullback_ofOriginal (i : a.Index)
    (h : _root_.id '' Set.range (chart a (Index.ofOriginal a i)) ⊆ Set.range (a.chart i)) :
    (toOriginal a hd).pullback
        (ULift.up (Index.ofOriginal a i) : (presentation a hd).atlas.Index)
        (ULift.up i : (originalPresentation a).atlas.Index) h =
      (originalAlgebraEquiv a hd i).toBoundedAlgHom :=
  (originalAlgebraEquiv_toBoundedAlgHom a hd i (fun x hx => h ⟨x, hx, rfl⟩)).symm

/-- Mixed comparison restrictions compose to the entire original restriction. -/
theorem fromOriginalInclusion_comp_toOriginalInclusion
    (i : a.Index) (s : Index a) (j : a.Index)
    (hf : Set.range (a.chart i) ⊆ Set.range (chart a s))
    (hg : Set.range (chart a s) ⊆ Set.range (a.chart j))
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    (fromOriginalInclusion a hd i s hf).restriction.comp
        (toOriginalInclusion a hd s j hg).restriction =
      a.restriction i j h :=
  congrArg Inclusion.restriction
    (@Subsingleton.elim (Inclusion (originalChart a hd i) (originalChart a hd j))
      inferInstance
      (fromOriginalInclusion a hd i s hf ≫ toOriginalInclusion a hd s j hg)
      (originalInclusion a hd i j h))

/-- The other mixed composite is the entire constructed rational restriction. -/
theorem toOriginalInclusion_comp_fromOriginalInclusion
    (s : Index a) (i : a.Index) (r : Index a)
    (hf : Set.range (chart a s) ⊆ Set.range (a.chart i))
    (hg : Set.range (a.chart i) ⊆ Set.range (chart a r))
    (h : Set.range (chart a s) ⊆ Set.range (chart a r)) :
    (toOriginalInclusion a hd s i hf).restriction.comp
        (fromOriginalInclusion a hd i r hg).restriction =
      restriction a hd s r h :=
  congrArg Inclusion.restriction
    (@Subsingleton.elim (Inclusion (s.directedDomain a hd) (r.directedDomain a hd))
      inferInstance
      (toOriginalInclusion a hd s i hf ≫ fromOriginalInclusion a hd i r hg)
      (inclusion a hd s r h))

/-- Directedness of the original atlas survives its index lift. -/
def originalDirectedPresentation : DirectedAtlasPresentation.{u, v, max v w} K where
  presentation := originalPresentation a
  directed i j := by
    change ULift.{v} a.Index at i j
    obtain ⟨q, hiq, hjq⟩ := hd i.down j.down
    exact ⟨ULift.up q, hiq, hjq⟩

/-- The constructed rational atlas is directed after its index lift. -/
def directedPresentation : DirectedAtlasPresentation.{u, v, max v w} K where
  presentation := presentation a hd
  directed s r := by
    change ULift.{w} (Index a) at s r
    obtain ⟨q, hsq, hrq⟩ := atlas_hasDirectedCharts a hd s.down r.down
    exact ⟨ULift.up q, hsq, hrq⟩

/-- The original-to-rational-to-original round trip is the whole identity
strong morphism, including every admissible bounded pullback. -/
theorem fromOriginal_comp_toOriginal :
    (fromOriginal a hd).compOfDirected (toOriginal a hd)
        (directedPresentation a hd).directed
        (originalDirectedPresentation a hd).directed =
      StrongHom.id (originalPresentation a) := by
  refine StrongHom.ext_of_directed
    (originalDirectedPresentation a hd).directed rfl ?_
  intro i
  change ULift.{v} a.Index at i
  let s : (presentation a hd).atlas.Index := ULift.up (Index.ofOriginal a i.down)
  have hf : (fromOriginal a hd).baseMap '' Set.range ((originalPresentation a).atlas.chart i) ⊆
      Set.range ((presentation a hd).atlas.chart s) := by
    change _root_.id '' Set.range (a.chart i.down) ⊆
      Set.range ((atlas a hd).chart (Index.ofOriginal a i.down))
    rw [Set.image_id, atlas_ofOriginal_range]
  have hg : (toOriginal a hd).baseMap '' Set.range ((presentation a hd).atlas.chart s) ⊆
      Set.range ((originalPresentation a).atlas.chart i) := by
    change _root_.id '' Set.range ((atlas a hd).chart (Index.ofOriginal a i.down)) ⊆
      Set.range (a.chart i.down)
    rw [Set.image_id, atlas_ofOriginal_range]
  have h := (fromOriginal a hd).comp_admissible (toOriginal a hd) i s i hf hg
  refine ⟨i, h, ?_⟩
  rw [StrongHom.compOfDirected_pullback (fromOriginal a hd) (toOriginal a hd)
    (directedPresentation a hd).directed
    (originalDirectedPresentation a hd).directed i s i hf hg h]
  exact fromOriginalInclusion_comp_toOriginalInclusion a hd i.down s.down i.down
    (fun x hx => hf ⟨x, hx, rfl⟩) (fun x hx => hg ⟨x, hx, rfl⟩)
    (fun x hx => h ⟨x, hx, rfl⟩)

/-- The rational-to-original-to-rational round trip is the whole rational
identity strong morphism, with no greatest-chart or nonempty-index assumption. -/
theorem toOriginal_comp_fromOriginal :
    (toOriginal a hd).compOfDirected (fromOriginal a hd)
        (originalDirectedPresentation a hd).directed
        (directedPresentation a hd).directed =
      StrongHom.id (presentation a hd) := by
  refine StrongHom.ext_of_directed (directedPresentation a hd).directed rfl ?_
  intro s
  change ULift.{w} (Index a) at s
  let i : (originalPresentation a).atlas.Index := ULift.up (s.down.original a)
  let r : (presentation a hd).atlas.Index := ULift.up (Index.ofOriginal a (s.down.original a))
  have hf : (toOriginal a hd).baseMap '' Set.range ((presentation a hd).atlas.chart s) ⊆
      Set.range ((originalPresentation a).atlas.chart i) := by
    change _root_.id '' Set.range (chart a s.down) ⊆ Set.range (a.chart (s.down.original a))
    rw [Set.image_id, range_chart, ← s.down.locus_original_rational a]
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hg : (fromOriginal a hd).baseMap '' Set.range ((originalPresentation a).atlas.chart i) ⊆
      Set.range ((presentation a hd).atlas.chart r) := by
    change _root_.id '' Set.range (a.chart (s.down.original a)) ⊆
      Set.range ((atlas a hd).chart (Index.ofOriginal a (s.down.original a)))
    rw [Set.image_id, atlas_ofOriginal_range]
  have h := (toOriginal a hd).comp_admissible (fromOriginal a hd) s i r hf hg
  refine ⟨r, h, ?_⟩
  rw [StrongHom.compOfDirected_pullback (toOriginal a hd) (fromOriginal a hd)
    (originalDirectedPresentation a hd).directed
    (directedPresentation a hd).directed s i r hf hg h]
  exact toOriginalInclusion_comp_fromOriginalInclusion a hd s.down i.down r.down
    (fun x hx => hf ⟨x, hx, rfl⟩) (fun x hx => hg ⟨x, hx, rfl⟩)
    (fun x hx => h ⟨x, hx, rfl⟩)

/-- The explicit full strong comparisons are an actual isomorphism in the
category of directed atlas presentations. -/
def directedIso : originalDirectedPresentation a hd ≅ directedPresentation a hd where
  hom := fromOriginal a hd
  inv := toOriginal a hd
  hom_inv_id := fromOriginal_comp_toOriginal a hd
  inv_hom_id := toOriginal_comp_fromOriginal a hd

@[simp]
theorem directedIso_hom : (directedIso a hd).hom = fromOriginal a hd := rfl

@[simp]
theorem directedIso_inv : (directedIso a hd).inv = toOriginal a hd := rfl

@[simp]
theorem directedIso_hom_baseMap :
    (directedIso a hd).hom.baseMap = ContinuousMap.id X := rfl

@[simp]
theorem directedIso_inv_baseMap :
    (directedIso a hd).inv.baseMap = ContinuousMap.id X := rfl

end Langlands.Analytic.DirectedRationalAtlas
