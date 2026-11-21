import Langlands.Geometry.Analytic.GroundFieldExtensionQuasiIsoStatement
import Langlands.Geometry.Analytic.GroundFieldExtensionFunctor
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms
import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph

/-! # Ground field extension preserves strong quasi-isomorphisms -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open IndexedAffinoidAtlas.GroundFieldExtension

set_option maxHeartbeats 1000000 in
/-- The actual scalar extension of a compatible strong quasi-isomorphism is a
strong quasi-isomorphism. -/
theorem groundFieldExtensionQuasiIso : GroundFieldExtensionQuasiIsoStatement.{u, v, w, u'} := by
  intro K _ _ _ L _ _ _ _ A B f hf
  let AL := presentation K L A.atlas
  let BL := presentation K L B.atlas
  let g : StrongHom AL BL := (compatibleMap K L f).toStrongHom
  let pA : AL.space → A.space := projection K L A.atlas
  let pB : BL.space → B.space := projection K L B.atlas
  have hnat (x : AL.space) : pB (g.baseMap x) = f.baseMap (pA x) :=
    projection_pointMap K L f.toStrongHom f.compatible x
  have hrA (i : A.atlas.Index) : range (AL.atlas.chart i) = pA ⁻¹' range (A.atlas.chart i) :=
    range_chart K L A.atlas i
  have hrB (j : B.atlas.Index) : range (BL.atlas.chart j) = pB ⁻¹' range (B.atlas.chart j) :=
    range_chart K L B.atlas j
  have hrep (i : A.atlas.Index) (j : B.atlas.Index)
      (h : g.baseMap '' range (AL.atlas.chart i) ⊆ range (BL.atlas.chart j)) :
      Represents L (g.pullback i j h)
        (spectrumProjection K L (B.atlas.algebra j) ⁻¹' f.toStrongHom.chartImageLocus i j) := by
    let h₀ := (admissible_iff K L f.toStrongHom f.compatible i j).mp h
    exact domainPreservation.{u, u'} K L _ _ _ _ (hf.2 i j h₀)
  have himage (i : A.atlas.Index) : g.baseMap '' range (AL.atlas.chart i) =
      pB ⁻¹' (f.baseMap '' range (A.atlas.chart i)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ pA ⁻¹' range (A.atlas.chart i) := (hrA i) ▸ hx
      exact ⟨pA x, hx', (hnat x).symm⟩
    · intro hz
      obtain ⟨j, hj⟩ := f.target_exists i
      let hL : g.baseMap '' range (AL.atlas.chart i) ⊆ range (BL.atlas.chart j) :=
        (admissible_iff K L f.toStrongHom f.compatible i j).mpr hj
      have hzj : z ∈ range (BL.atlas.chart j) := (hrB j).symm ▸ hj hz
      obtain ⟨t, rfl⟩ := hzj
      have ht : t ∈ range (BanachSpectrum.comap (g.pullback i j hL).toBoundedRingHom) := by
        rw [(hrep i j hL).2.1]
        exact hz
      obtain ⟨s, hs⟩ := ht
      refine ⟨AL.atlas.chart i s, ⟨s, rfl⟩, ?_⟩
      exact (g.chart_comm i j hL s).symm.trans (congrArg (BL.atlas.chart j) hs)
  have hemb (i : A.atlas.Index) :
      IsEmbedding ((g.baseMap : AL.space → BL.space) ∘ AL.atlas.chart i) := by
    obtain ⟨j, hj⟩ := g.target_exists i
    have hi := PresentedAffinoidAlgebra.GroundFieldExtension.comap_injective_of_represents
      (hrep i j hj)
    have hc := (BanachSpectrum.comapContinuous (g.pullback i j hj).toBoundedRingHom).continuous
    have hEmb := (BL.atlas.isEmbedding_chart j).comp (hc.isClosedEmbedding hi).isEmbedding
    have hcomp : BL.atlas.chart j ∘ BanachSpectrum.comap (g.pullback i j hj).toBoundedRingHom =
        g.baseMap ∘ AL.atlas.chart i := funext (g.chart_comm i j hj)
    exact hcomp ▸ hEmb
  have hinj : Function.Injective g.baseMap := by
    intro x y hxy
    have hproj : pA x = pA y := hf.1.isEmbedding.injective
      ((hnat x).symm.trans ((congrArg pB hxy).trans (hnat y)))
    obtain ⟨i, s, rfl⟩ := (chartSystem K L A.atlas).exists_chart x
    have hx : AL.atlas.chart i s ∈ range (AL.atlas.chart i) := ⟨s, rfl⟩
    have hx' : AL.atlas.chart i s ∈ pA ⁻¹' range (A.atlas.chart i) := (hrA i) ▸ hx
    have hy' : pA y ∈ range (A.atlas.chart i) := hproj ▸ hx'
    have hy : y ∈ range (AL.atlas.chart i) :=
      (hrA i).symm ▸ (show y ∈ pA ⁻¹' range (A.atlas.chart i) from hy')
    obtain ⟨t, rfl⟩ := hy
    exact congrArg (AL.atlas.chart i) ((hemb i).injective hxy)
  let e₀ := hf.1.homeomorph f.baseMap
  let τ₀ := range (fun i : A.atlas.Index => range (A.atlas.chart i))
  let τ : Set (Set BL.space) := (Set.preimage pB) '' AtlasTopology.imageFamily e₀ τ₀
  have hτ : AtlasTopology.IsQuasinet τ :=
    (A.atlas.isNet_chartFamily.1.imageFamily e₀).preimage_image (continuous_projection K L B.atlas)
  have hτMem {V : Set BL.space} (hV : V ∈ τ) :
      ∃ i : A.atlas.Index, V = g.baseMap '' range (AL.atlas.chart i) := by
    obtain ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩ := hV
    exact ⟨i, (himage i).symm⟩
  have hsurj : Function.Surjective g.baseMap := by
    intro y
    obtain ⟨V, hV, hy⟩ := Set.mem_sUnion.mp (show y ∈ ⋃₀ τ from hτ.covers.symm ▸ mem_univ y)
    obtain ⟨i, rfl⟩ := hτMem hV
    obtain ⟨x, _, hxy⟩ := hy
    exact ⟨x, hxy⟩
  let e : AL.space ≃ BL.space := Equiv.ofBijective g.baseMap ⟨hinj, hsurj⟩
  have hInv : Continuous e.symm := by
    apply hτ.continuous
    intro V hV
    obtain ⟨i, rfl⟩ := hτMem hV
    rw [← range_comp]
    apply continuousOn_iff_continuous_domRestrict.mpr
    let eᵢ := (hemb i).toHomeomorph
    have heq : (range ((g.baseMap : AL.space → BL.space) ∘ AL.atlas.chart i)).domRestrict e.symm =
        AL.atlas.chart i ∘ eᵢ.symm := by
      funext z
      apply e.injective
      change e (e.symm z) = (g.baseMap : AL.space → BL.space) (AL.atlas.chart i (eᵢ.symm z))
      rw [Equiv.apply_symm_apply]
      exact (congrArg Subtype.val (eᵢ.apply_symm_apply z)).symm
    rw [heq]
    exact (AL.atlas.isEmbedding_chart i).continuous.comp eᵢ.symm.continuous
  refine ⟨isHomeomorph_iff_exists_inverse.mpr
    ⟨g.baseMap.continuous, e.symm, e.left_inv, e.right_inv, hInv⟩, ?_⟩
  intro i j h
  rw [← g.range_pullback i j h]
  exact PresentedAffinoidAlgebra.GroundFieldExtension.represents_range (hrep i j h)

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
