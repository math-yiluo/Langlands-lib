import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry
import Langlands.AlgebraicGeometry.GeometricallyConnectedConstructibilityFromGeneric
import Langlands.AlgebraicGeometry.ClosedSubschemeSupportGeometry

/-! # The closure of a section-selected generic component -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

variable {X Y : Scheme.{u}}

/-- The actual closure in the total space of the component selected in one residue fibre. -/
def componentClosure (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) (y : Y) :
    TopologicalSpace.Closeds X :=
  ⟨closure ((f.fiberι y) '' connectedComponent (fiberPoint f e he y)), isClosed_closure⟩

/-- Taking the closure in the total space does not alter its trace on the original fibre. -/
theorem preimage_componentClosure (f : X ⟶ Y) (e : Y ⟶ X)
    (he : e ≫ f = 𝟙 Y) (y : Y) :
    (f.fiberι y) ⁻¹' (componentClosure f e he y : Set X) =
      connectedComponent (fiberPoint f e he y) := by
  change (f.fiberι y) ⁻¹' closure ((f.fiberι y) ''
    connectedComponent (fiberPoint f e he y)) = _
  rw [← (f.fiberι y).isEmbedding.closure_eq_preimage_closure_image,
    isClosed_connectedComponent.closure_eq]

/-- Generic geometric-connectedness constancy identifies the selected-component union
near the generic fibre with the actual closure of that fibre's selected component. -/
theorem exists_open_componentClosure_eq_componentSet
    (H : SchemeFiberGeometry.NoetherianGeometricallyConnectedFiberGenericConstancy.{u})
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) {η : Y}
    (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ W : Set Y, IsOpen W ∧ η ∈ W ∧
      f ⁻¹' W ∩ componentSet f e he =
        f ⁻¹' W ∩ (componentClosure f e he η : Set X) := by
  classical
  let C₀ : TopologicalSpace.Closeds (f.fiber η) :=
    ⟨connectedComponent (fiberPoint f e he η), isClosed_connectedComponent⟩
  let C₁ : TopologicalSpace.Closeds (f.fiber η) :=
    ⟨(connectedComponent (fiberPoint f e he η))ᶜ,
      (fiberComponentOpen f e he η).isOpen.isClosed_compl⟩
  let C : Bool → TopologicalSpace.Closeds (f.fiber η) :=
    fun b => if b then C₀ else C₁
  let g := fun b => GenericImagePattern.fiberClosedSubsetClosureι f η (C b)
  have hg₀ : Set.range (g true) = (componentClosure f e he η : Set X) := by
    exact GenericImagePattern.range_fiberClosedSubsetClosureι f η C₀
  have hcover : (⋃ b, (C b : Set (f.fiber η))) = Set.univ := by
    ext z
    simp [C, C₀, C₁, Bool.exists_bool, em']
  obtain ⟨V, hV, hηV, hpattern⟩ :=
    GenericImagePattern.exists_open_fiberClosedSubsetClosures_cover_and_incidence
      f hη C hcover
  let U := fiberComponentOpen f e he η
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact isClosed_connectedComponent)
  have hgc : GeometricallyConnected
      ((g true ≫ f).fiberToSpecResidueField η) := by
    apply (GenericImagePattern.geometricallyConnected_fiberClosedSubsetClosure_iff
      f η C₀).mpr
    have hh := GenericImagePattern.geometricallyConnected_iff_of_closedImmersion_range_eq
      (f.fiberToSpecResidueField η)
      (Scheme.IdealSheafData.vanishingIdeal C₀).subschemeι U.ι (by
        rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Opens.range_ι]
        rfl)
    exact hh.mpr (geometricallyConnected_fiberComponentOpen f e he η)
  obtain ⟨V', hV', hηV', hconst⟩ := H (g true ≫ f) η hη
  have hηe : e η ∉ Set.range (g false) := by
    rw [← fiberι_fiberPoint f e he η]
    change fiberPoint f e he η ∉
      (f.fiberι η) ⁻¹' Set.range (g false)
    rw [GenericImagePattern.preimage_range_fiberClosedSubsetClosureι]
    exact fun h => h mem_connectedComponent
  let E : Set Y := (e ⁻¹' Set.range (g false))ᶜ
  have hE : IsOpen E :=
    ((g false).isClosedEmbedding.isClosed_range.preimage e.continuous).isOpen_compl
  let W := (V ∩ V') ∩ E
  refine ⟨W, (hV.inter hV').inter hE, ⟨⟨hηV, hηV'⟩, hηe⟩, ?_⟩
  have hfiber (y : Y) (hy : y ∈ W) :
      (f.fiberι y) ⁻¹' Set.range (g true) =
        connectedComponent (fiberPoint f e he y) := by
    let A : Bool → Set (f.fiber y) :=
      GenericImagePattern.fiberSubschemeSets f g y
    have hc : A true ∪ A false = Set.univ := by
      have hh := (hpattern y hy.1.1).1
      change (⋃ b, A b) = Set.univ at hh
      ext z
      have hz := Set.eq_univ_iff_forall.mp hh z
      rcases Set.mem_iUnion.mp hz with ⟨b, hb⟩
      cases b
      · exact iff_true_intro (Or.inr hb)
      · exact iff_true_intro (Or.inl hb)
    have hd : Disjoint (A true) (A false) := by
      apply Set.disjoint_iff_inter_eq_empty.mpr
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hh
      have hh' := ((hpattern y hy.1.1).2 true false).mp hh
      simp [C, C₀, C₁] at hh'
    have hp : fiberPoint f e he y ∈ A true := by
      have hp' := Set.eq_univ_iff_forall.mp hc (fiberPoint f e he y)
      rcases hp' with ht | hf
      · exact ht
      · exact False.elim (hy.2 (by
          change f.fiberι y (fiberPoint f e he y) ∈ Set.range (g false) at hf
          rwa [fiberι_fiberPoint] at hf))
    have hclosed (b : Bool) : IsClosed (A b) :=
      (g b).isClosedEmbedding.isClosed_range.preimage (f.fiberι y).continuous
    have hopen : IsOpen (A true) := by
      have heq : (A true)ᶜ = A false := by
        ext z
        have hz := Set.eq_univ_iff_forall.mp hc z
        exact ⟨fun hn => hz.resolve_left hn,
          fun hf ht => Set.disjoint_left.mp hd ht hf⟩
      rw [← isClosed_compl_iff, heq]
      exact hclosed false
    have hcy : ConnectedSpace ((g true ≫ f).fiber y) := by
      have : GeometricallyConnected ((g true ≫ f).fiberToSpecResidueField y) :=
        (hconst y hy.1.2).mpr hgc
      exact GeometricallyConnected.connectedSpace_of_subsingleton
        ((g true ≫ f).fiberToSpecResidueField y)
    have : ConnectedSpace ↥(pullback (g true) (f.fiberι y)) :=
      (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) (g true)).hom.homeomorph
        |>.connectedSpace_iff.mpr hcy
    have hconn : _root_.IsConnected (A true) := by
      change _root_.IsConnected ((f.fiberι y) ⁻¹' Set.range (g true))
      rw [← Scheme.Pullback.range_snd, ← Set.image_univ]
      exact isConnected_univ.image _ (pullback.snd (g true) (f.fiberι y)).continuous.continuousOn
    exact Set.Subset.antisymm (hconn.subset_connectedComponent hp)
      ((show IsClopen (A true) from ⟨hclosed true, hopen⟩).connectedComponent_subset hp)
  ext x
  constructor
  · rintro ⟨hxW, hx⟩
    obtain ⟨y, z, hz, rfl⟩ := hx
    refine ⟨hxW, ?_⟩
    rw [← hg₀]
    apply (Set.ext_iff.mp (hfiber y ?_) z).mpr hz
    simpa only [Set.mem_preimage, structure_fiberι] using hxW
  · rintro ⟨hxW, hxC⟩
    have hx : x ∈ Set.range (f.fiberι (f x)) := by
      rw [Scheme.Hom.range_fiberι]
      rfl
    obtain ⟨z, hz⟩ := hx
    have hzC : z ∈ (f.fiberι (f x)) ⁻¹' Set.range (g true) := by
      change f.fiberι (f x) z ∈ Set.range (g true)
      rw [hz, hg₀]
      exact hxC
    exact ⟨hxW, f x, z, (Set.ext_iff.mp (hfiber _ hxW) z).mp hzC, hz⟩

end Langlands.AlgebraicGeometry.SectionComponent
