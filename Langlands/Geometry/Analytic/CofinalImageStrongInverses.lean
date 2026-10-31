import Langlands.Geometry.Analytic.StrongQuasiIsoCancellation
import Langlands.Geometry.Analytic.StrongQuasiIsoComposition

/-! # Strong inverses for quasi-isomorphisms with upper-cofinal chart images -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Every original target chart is contained in the image of an original
source chart. This is an additional condition on the supplied atlases. -/
def HasUpperCofinalImage (f : StrongHom A B) : Prop :=
  ∀ j : B.atlas.Index, ∃ i : A.atlas.Index,
    Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)

namespace IsQuasiIso

variable {f : StrongHom A B} (hf : f.IsQuasiIso)

include hf in
/-- Full domain factorization constructs one bounded reverse pullback,
characterized in every original chart containing both relevant loci. -/
theorem inversePullback_existsUnique (hb : B.atlas.HasDirectedCharts)
    (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)) :
    ∃! ψ : BoundedAlgHom K (A.atlas.algebra i) (B.atlas.algebra j),
      ∀ (q : B.atlas.Index)
        (hfq : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart q))
        (hjq : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q)),
        ψ.comp (f.pullback i q hfq) = B.atlas.restriction j q hjq := by
  obtain ⟨q₀, hf₀⟩ := f.target_exists i
  obtain ⟨q, h₀q, hjq⟩ := hb q₀ j
  have hfq := hf₀.trans h₀q
  have hφ : PresentedAffinoidAlgebra.HasImageIn K (B.atlas.restriction j q hjq)
      (f.chartImageLocus i q) := by
    intro x
    change B.atlas.chart q
      (BanachSpectrum.comap (B.atlas.restriction j q hjq).toBoundedRingHom x) ∈
        f.baseMap '' Set.range (A.atlas.chart i)
    rw [B.atlas.restriction_chart]
    exact h ⟨x, rfl⟩
  obtain ⟨ψ, hψ, _⟩ := (hf.2 i q hfq).2.2 (B.atlas.algebra j)
    (B.atlas.restriction j q hjq) hφ
  refine ⟨ψ, ?_, ?_⟩
  · intro r hfr hjr
    obtain ⟨s, hqs, hrs⟩ := hb q r
    have hfs := hfq.trans hqs
    apply B.atlas.restriction_hom_ext r s hrs (B.atlas.algebra j)
    calc
      (ψ.comp (f.pullback i r hfr)).comp (B.atlas.restriction r s hrs) =
          ψ.comp (f.pullback i s hfs) := by
        rw [BoundedAlgHom.comp_assoc, ← f.pullback_comp_restriction i r s hrs hfr hfs]
      _ = (ψ.comp (f.pullback i q hfq)).comp (B.atlas.restriction q s hqs) := by
        rw [BoundedAlgHom.comp_assoc, ← f.pullback_comp_restriction i q s hqs hfq hfs]
      _ = B.atlas.restriction j s (hjq.trans hqs) := by
        rw [hψ, ← B.atlas.restriction_comp]
      _ = (B.atlas.restriction j r hjr).comp (B.atlas.restriction r s hrs) :=
        B.atlas.restriction_comp j r s hjr hrs _
  · intro χ hχ
    apply (hf.2 i q hfq).hom_ext (B.atlas.algebra j)
    exact (hχ q hfq hjq).trans hψ.symm

/-- The bounded reverse map uses the actual original chart algebras. -/
def inversePullback (hb : B.atlas.HasDirectedCharts)
    (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i)) :
    BoundedAlgHom K (A.atlas.algebra i) (B.atlas.algebra j) :=
  Classical.choose (hf.inversePullback_existsUnique hb j i h).exists

/-- The reverse map factors each original target restriction through the
given forward bounded pullback, for every containing chart. -/
theorem inversePullback_comp_pullback (hb : B.atlas.HasDirectedCharts)
    (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i))
    (q : B.atlas.Index)
    (hfq : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart q))
    (hjq : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q)) :
    (hf.inversePullback hb j i h).comp (f.pullback i q hfq) =
      B.atlas.restriction j q hjq :=
  Classical.choose_spec (hf.inversePullback_existsUnique hb j i h).exists q hfq hjq

/-- The exact spectrum square follows from the bounded factorization equation. -/
theorem inversePullback_chart (hb : B.atlas.HasDirectedCharts)
    (j : B.atlas.Index) (i : A.atlas.Index)
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i))
    (x : BanachSpectrum (B.atlas.algebra j)) :
    f.baseMap (A.atlas.chart i
      (BanachSpectrum.comap (hf.inversePullback hb j i h).toBoundedRingHom x)) =
        B.atlas.chart j x := by
  obtain ⟨q₀, hf₀⟩ := f.target_exists i
  obtain ⟨q, h₀q, hjq⟩ := hb q₀ j
  have hfq := hf₀.trans h₀q
  have heq := congrArg
    (fun φ : BoundedAlgHom K (B.atlas.algebra q) (B.atlas.algebra j) =>
      B.atlas.chart q (BanachSpectrum.comap φ.toBoundedRingHom x))
    (hf.inversePullback_comp_pullback hb j i h q hfq hjq)
  change B.atlas.chart q
      (BanachSpectrum.comap (f.pullback i q hfq).toBoundedRingHom
        (BanachSpectrum.comap (hf.inversePullback hb j i h).toBoundedRingHom x)) =
      B.atlas.chart q
        (BanachSpectrum.comap (B.atlas.restriction j q hjq).toBoundedRingHom x) at heq
  rwa [f.chart_comm, B.atlas.restriction_chart] at heq

/-- Reverse pullbacks commute with both original atlas restrictions as
bounded algebra maps, by full domain uniqueness. -/
theorem inversePullback_naturality (hb : B.atlas.HasDirectedCharts)
    (j j' : B.atlas.Index) (i i' : A.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i))
    (h' : Set.range (B.atlas.chart j') ⊆ f.baseMap '' Set.range (A.atlas.chart i')) :
    (B.atlas.restriction j j' hj).comp (hf.inversePullback hb j' i' h') =
      (hf.inversePullback hb j i h).comp (A.atlas.restriction i i' hi) := by
  obtain ⟨q₀, hf₀⟩ := f.target_exists i'
  obtain ⟨q, h₀q, hj'q⟩ := hb q₀ j'
  have hfi'q := hf₀.trans h₀q
  have hfiq := (Set.image_mono hi).trans hfi'q
  have hjq := hj.trans hj'q
  apply (hf.2 i' q hfi'q).hom_ext (B.atlas.algebra j)
  rw [BoundedAlgHom.comp_assoc,
    hf.inversePullback_comp_pullback hb j' i' h' q hfi'q hj'q,
    ← B.atlas.restriction_comp j j' q hj hj'q hjq,
    BoundedAlgHom.comp_assoc, f.restriction_comp_pullback i i' q hi hfiq hfi'q,
    hf.inversePullback_comp_pullback hb j i h q hfiq hjq]

/-- The continuous inverse of the actual ambient homeomorphism. -/
def inverseBaseMap : C(B.space, A.space) :=
  ⟨hf.1.homeomorph.symm, hf.1.homeomorph.symm.continuous⟩

@[simp]
theorem baseMap_inverseBaseMap (x : B.space) :
    f.baseMap (hf.inverseBaseMap x) = x :=
  hf.1.homeomorph.apply_symm_apply x

@[simp]
theorem inverseBaseMap_baseMap (x : A.space) :
    hf.inverseBaseMap (f.baseMap x) = x :=
  hf.1.homeomorph.symm_apply_apply x

/-- Reverse admissibility is exactly containment in a forward chart image. -/
theorem inverse_admissible_iff (j : B.atlas.Index) (i : A.atlas.Index) :
    hf.inverseBaseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (A.atlas.chart i) ↔
      Set.range (B.atlas.chart j) ⊆ f.baseMap '' Set.range (A.atlas.chart i) := by
  constructor
  · intro h y hy
    exact ⟨hf.inverseBaseMap y, h ⟨y, hy, rfl⟩, hf.baseMap_inverseBaseMap y⟩
  · intro h
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h hy
    rw [← hxy, hf.inverseBaseMap_baseMap]
    exact hx

/-- An actual full reverse strong map. Upper cofinality supplies targets;
every admissible bounded pullback is constructed by domain factorization. -/
def inverse (hb : B.atlas.HasDirectedCharts) (hc : f.HasUpperCofinalImage) :
    StrongHom B A where
  baseMap := hf.inverseBaseMap
  target_exists j := by
    obtain ⟨i, hi⟩ := hc j
    exact ⟨i, (hf.inverse_admissible_iff j i).mpr hi⟩
  pullback j i h := hf.inversePullback hb j i ((hf.inverse_admissible_iff j i).mp h)
  chart_comm j i h x := by
    apply hf.1.injective
    rw [hf.inversePullback_chart, hf.baseMap_inverseBaseMap]
  restriction_comm j j' i i' hj hi h h' :=
    hf.inversePullback_naturality hb j j' i i' hj hi
      ((hf.inverse_admissible_iff j i).mp h)
      ((hf.inverse_admissible_iff j' i').mp h')

@[simp]
theorem inverse_baseMap (hb : B.atlas.HasDirectedCharts) (hc : f.HasUpperCofinalImage) :
    (hf.inverse hb hc).baseMap = hf.inverseBaseMap := rfl

@[simp]
theorem inverse_pullback (hb : B.atlas.HasDirectedCharts) (hc : f.HasUpperCofinalImage)
    (j : B.atlas.Index) (i : A.atlas.Index)
    (h : (hf.inverse hb hc).baseMap '' Set.range (B.atlas.chart j) ⊆
      Set.range (A.atlas.chart i)) :
    (hf.inverse hb hc).pullback j i h =
      hf.inversePullback hb j i ((hf.inverse_admissible_iff j i).mp h) := rfl

/-- Each reverse pullback represents its full image domain against every
presented affinoid test algebra, by descent from an original restriction. -/
theorem inverse_isQuasiIso (hb : B.atlas.HasDirectedCharts) (hc : f.HasUpperCofinalImage) :
    (hf.inverse hb hc).IsQuasiIso := by
  refine ⟨hf.1.homeomorph.symm.isHomeomorph, ?_⟩
  intro j i h
  obtain ⟨q₀, hf₀⟩ := f.target_exists i
  obtain ⟨q, h₀q, hjq⟩ := hb q₀ j
  have hfq := hf₀.trans h₀q
  have hcomp : PresentedAffinoidAlgebra.Represents K
      (((hf.inverse hb hc).pullback j i h).comp (f.pullback i q hfq))
      (B.atlas.chart q ⁻¹' Set.range (B.atlas.chart j)) := by
    rw [inverse_pullback, hf.inversePullback_comp_pullback hb j i _ q hfq hjq]
    exact B.atlas.restriction_represents j q hjq
  have hrep := (hf.2 i q hfq).of_comp_of_injective hcomp
    (hf.isEmbedding_pullback i q hfq).injective
  have hlocus : (BanachSpectrum.comap (f.pullback i q hfq).toBoundedRingHom) ⁻¹'
      (B.atlas.chart q ⁻¹' Set.range (B.atlas.chart j)) =
        (hf.inverse hb hc).chartImageLocus j i := by
    ext x
    change B.atlas.chart q
      (BanachSpectrum.comap (f.pullback i q hfq).toBoundedRingHom x) ∈
        Set.range (B.atlas.chart j) ↔
      A.atlas.chart i x ∈ hf.inverseBaseMap '' Set.range (B.atlas.chart j)
    rw [f.chart_comm]
    constructor
    · intro hx
      exact ⟨f.baseMap (A.atlas.chart i x), hx, hf.inverseBaseMap_baseMap _⟩
    · rintro ⟨y, hy, heq⟩
      have heq' := congrArg f.baseMap heq
      rw [hf.baseMap_inverseBaseMap] at heq'
      exact heq' ▸ hy
  rwa [hlocus] at hrep

/-- The reverse map followed by the original is the full strong identity. -/
theorem inverse_comp (ha : A.atlas.HasDirectedCharts) (hb : B.atlas.HasDirectedCharts)
    (hc : f.HasUpperCofinalImage) :
    (hf.inverse hb hc).compOfDirected f ha hb = StrongHom.id B := by
  have hbase : ((hf.inverse hb hc).compOfDirected f ha hb).baseMap =
      (StrongHom.id B).baseMap := by
    ext x
    exact hf.baseMap_inverseBaseMap x
  refine ext_of_directed (f := (hf.inverse hb hc).compOfDirected f ha hb)
    (g := StrongHom.id B) hb hbase ?_
  intro j
  obtain ⟨i, hi⟩ := hc j
  obtain ⟨q, hfq⟩ := f.target_exists i
  have hinv := (hf.inverse_admissible_iff j i).mpr hi
  have hjq := hi.trans hfq
  have h := (hf.inverse hb hc).comp_admissible f j i q hinv hfq
  refine ⟨q, h, ?_⟩
  rw [compOfDirected_pullback _ _ ha hb j i q hinv hfq h]
  change (hf.inversePullback hb j i hi).comp (f.pullback i q hfq) =
    B.atlas.restriction j q hjq
  exact hf.inversePullback_comp_pullback hb j i _ q hfq hjq

/-- The original followed by the reverse is the full strong identity,
using algebraic cancellation along the original quasi-isomorphism. -/
theorem comp_inverse (ha : A.atlas.HasDirectedCharts) (hb : B.atlas.HasDirectedCharts)
    (hc : f.HasUpperCofinalImage) :
    f.compOfDirected (hf.inverse hb hc) hb ha = StrongHom.id A := by
  apply hf.cancel_compOfDirected ha hb
  rw [compOfDirected_assoc, hf.inverse_comp ha hb hc,
    compOfDirected_id, id_compOfDirected]

end IsQuasiIso

end AffinoidAtlasPresentation.StrongHom

namespace DirectedAtlasPresentation

variable {A B : DirectedAtlasPresentation.{u, v, w} K}

/-- A quasi-isomorphism with upper-cofinal chart images is an actual
isomorphism in the full directed strong-map category. -/
def cofinalImageIso (f : A ⟶ B) (hf : f.IsQuasiIso) (hc : f.HasUpperCofinalImage) :
    A ≅ B where
  hom := f
  inv := hf.inverse B.directed hc
  hom_inv_id := hf.comp_inverse A.directed B.directed hc
  inv_hom_id := hf.inverse_comp A.directed B.directed hc

@[simp]
theorem cofinalImageIso_hom (f : A ⟶ B) (hf : f.IsQuasiIso)
    (hc : f.HasUpperCofinalImage) :
    (cofinalImageIso f hf hc).hom = f := rfl

@[simp]
theorem cofinalImageIso_inv_baseMap (f : A ⟶ B) (hf : f.IsQuasiIso)
    (hc : f.HasUpperCofinalImage) :
    (cofinalImageIso f hf hc).inv.baseMap = hf.inverseBaseMap := rfl

end DirectedAtlasPresentation

end Langlands.Analytic
