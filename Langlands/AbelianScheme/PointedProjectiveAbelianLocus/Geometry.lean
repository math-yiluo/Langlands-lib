import Langlands.AbelianScheme.PointedProjectiveAbelianLocus.BaseChange
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry
import Langlands.AlgebraicGeometry.SectionComponentOpennessProof
import Langlands.AlgebraicGeometry.SmoothGeometricallyReducedProof
import Langlands.GroupScheme.ReducedBaseSmooth.DimensionBridge
import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange

/-! # Smooth connected geometry near a point of the abelian-scheme locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AbelianScheme.PointedProjectiveAbelianLocus

open Langlands.AlgebraicGeometry OpenCoverStructure

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- The image of a test scheme with smooth base change lies in the open obtained by
removing the image of the nonsmooth locus of a proper flat family. -/
private theorem exists_smooth_open [Flat p] [IsProper p] [LocallyOfFinitePresentation p]
    {T : Scheme.{u}} (t : T ⟶ S) [Smooth (pullback.snd p t)] :
    ∃ U : S.Opens, Set.range t ⊆ U ∧ Smooth (pullback.snd p U.ι) := by
  let U : S.Opens :=
    ⟨(p '' (p.smoothLocus : Set X)ᶜ)ᶜ, (p.isClosedMap _ p.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩
  have hU : Set.range t ⊆ U := by
    intro y hy
    rintro ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ : x ∈ Set.range (pullback.fst p t) := by
      rwa [Scheme.Pullback.range_fst]
    have htop : pullback.fst p t ⁻¹ᵁ p.smoothLocus = ⊤ := by
      rw [← Scheme.Hom.smoothLocus_eq_preimage_of_isPullback
        (IsPullback.of_hasPullback p t) (Or.inl ‹Flat p›)]
      exact (pullback.snd p t).smoothLocus_eq_top
    exact hx (show z ∈ pullback.fst p t ⁻¹ᵁ p.smoothLocus by rw [htop]; trivial)
  refine ⟨U, hU, (pullback.snd p U.ι).smoothLocus_eq_top_iff.mp ?_⟩
  rw [Scheme.Hom.smoothLocus_eq_preimage_of_isPullback
    (IsPullback.of_hasPullback p U.ι) (Or.inl ‹Flat p›)]
  apply top_unique
  intro z _
  change pullback.fst p U.ι z ∈ p.smoothLocus
  have hmem : p (pullback.fst p U.ι z) ∈ U := by
    have h : pullback.fst p U.ι z ∈ Set.range (pullback.fst p U.ι) := ⟨z, rfl⟩
    rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at h
  by_contra hn
  exact hmem ⟨_, hn, rfl⟩

private theorem range_fieldPoint {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) :
    Set.range t = {t (IsLocalRing.closedPoint K)} :=
  Set.range_eq_singleton fun z => congrArg t (Subsingleton.elim z (IsLocalRing.closedPoint K))

/-- For a smooth proper family with a section, the connected residue-fibre condition
holds on the open obtained by removing the image of the complement of the section
component. The section makes those fibres geometrically connected. -/
private theorem exists_connected_open [Smooth p] [IsProper p] {s : S ⟶ X} (hs : s ≫ p = 𝟙 S)
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)
    [ConnectedSpace ↥(pullback p t)] :
    ∃ U : S.Opens, Set.range t ⊆ U ∧ GeometricallyConnected (pullback.snd p U.ι) := by
  let C := SectionComponent.componentSet p s hs
  have hC : IsOpen C :=
    SectionComponent.flatFinitePresentationOpenness X S p s hs inferInstance inferInstance
      inferInstance inferInstance (smoothGeometricallyReduced X S p inferInstance)
  let U : S.Opens := ⟨(p '' Cᶜ)ᶜ, (p.isClosedMap _ hC.isClosed_compl).isOpen_compl⟩
  let y := t (IsLocalRing.closedPoint K)
  have hconn : _root_.IsConnected (p ⁻¹' {y}) := by
    have hc := isConnected_univ.image (pullback.fst p t) (pullback.fst p t).continuous.continuousOn
    rwa [Set.image_univ, Scheme.Pullback.range_fst, range_fieldPoint] at hc
  let : ConnectedSpace (p.fiber y) :=
    (p.fiberHomeo y).connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hconn)
  have hy : y ∈ U := by
    rintro ⟨x, hx, hxy⟩
    obtain ⟨z, rfl⟩ : x ∈ Set.range (p.fiberι y) := by rw [p.range_fiberι]; exact hxy
    exact hx ((SectionComponent.fiberι_mem_componentSet_iff p s hs y z).mpr (by
      rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial))
  have hgeom (v : S) (hv : v ∈ U) : GeometricallyConnected (p.fiberToSpecResidueField v) := by
    let c := SectionComponent.fiberPoint p s hs v
    have hc : connectedComponent c = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      refine (SectionComponent.fiberι_mem_componentSet_iff p s hs v z).mp ?_
      by_contra hn
      exact hv ⟨p.fiberι v z, hn, SectionComponent.structure_fiberι p v z⟩
    let : ConnectedSpace (p.fiber v) := connectedSpace_iff_connectedComponent.mpr ⟨c, hc⟩
    exact geometricallyConnected_of_connected_section (p.fiberToSpecResidueField v)
      (SectionComponent.fiberSection p s hs v) (SectionComponent.fiberSection_toSpec p s hs v)
  refine ⟨U, ?_, GeometricallyConnected.iff_geometricallyConnected_fiber _ |>.mpr ?_⟩
  · simpa [range_fieldPoint, y] using hy
  · intro v
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected.{u})
      (isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback p U.ι) v)
      (hgeom v.1 v.2)

/-- A field test with a pointed abelian scheme factors through a noetherian affine open
where the family is smooth of the prescribed dimension with geometrically connected fibres. -/
theorem exists_affine_geometry [IsLocallyNoetherian S] [Flat p] [IsProper p]
    [LocallyOfFinitePresentation p] {s : S ⟶ X} (hs : s ≫ p = 𝟙 S) {g : ℕ}
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)
    (ht : HasPointedAbelianPullback p s g t) :
    ∃ (R : CommRingCat.{u}) (_ : IsNoetherianRing R) (j : Spec R ⟶ S)
      (v : Spec (CommRingCat.of K) ⟶ Spec R),
        IsOpenImmersion j ∧ v ≫ j = t ∧
          SmoothOfRelativeDimension g (pullback.snd p j) ∧
          GeometricallyConnected (pullback.snd p j) := by
  obtain ⟨A, -, ⟨e⟩⟩ := (pointed_iff_overIso hs t).mp ht
  let : Smooth (pullback.snd p t) := baseChangeProperty_of_overIso @Smooth e.symm A.smooth
  obtain ⟨U, hU, hq⟩ := exists_smooth_open (p := p) t
  let u := IsOpenImmersion.lift U.ι t (by simpa only [Scheme.Opens.range_ι] using hU)
  have hu : u ≫ U.ι = t := IsOpenImmersion.lift_fac ..
  let q := pullback.snd p U.ι
  let : Smooth q := hq
  have htu : HasPointedAbelianPullback q (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection _ _ hs U.ι) g u :=
    (pointed_iterated hs U.ι u).mpr (by simpa only [hu] using ht)
  obtain ⟨A₁, -, ⟨e₁⟩⟩ :=
    (pointed_iff_overIso (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection_snd _ _ hs U.ι) u).mp htu
  let : GeometricallyConnected (pullback.snd q u) :=
    baseChangeProperty_of_overIso @GeometricallyConnected e₁.symm A₁.geometricallyConnected
  let : ConnectedSpace ↥(pullback q u) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd q u)
  obtain ⟨W, hW, hgeom⟩ := exists_connected_open (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection_snd _ _ hs U.ι) u
  let w := IsOpenImmersion.lift W.ι u (by simpa only [Scheme.Opens.range_ι] using hW)
  have hw : w ≫ W.ι = u := IsOpenImmersion.lift_fac ..
  let C := connectedComponentOpen W.toScheme (w (IsLocalRing.closedPoint K))
  let c := Langlands.AlgebraicGeometry.connectedComponentSection w
  have hc : c ≫ C.ι = w := Langlands.AlgebraicGeometry.connectedComponentSection_ι w
  let q' := pullback.snd q W.ι
  let : Smooth q' := inferInstanceAs (Smooth (pullback.snd q W.ι))
  let : GeometricallyConnected q' := hgeom
  let r := pullback.snd q' C.ι
  let : Smooth r := inferInstanceAs (Smooth (pullback.snd q' C.ι))
  let : GeometricallyConnected r := inferInstanceAs (GeometricallyConnected (pullback.snd q' C.ι))
  let : ConnectedSpace ↥C.toScheme := connectedSpace_connectedComponentOpen _ _
  have hr : ConnectedSpace ↥(pullback q' C.ι) := GeometricallyConnected.connectedSpace r r.isOpenMap
  obtain ⟨n, hn⟩ := smoothConnectedRelativeDimension _ _ r ‹Smooth r› hr
  let k := C.ι ≫ W.ι ≫ U.ι
  have hk : c ≫ k = t := by
    change c ≫ C.ι ≫ W.ι ≫ U.ι = t
    rw [← Category.assoc, hc, ← Category.assoc, hw, hu]
  let ek : (Over.pullback k).obj (Over.mk p) ≅ Over.mk r :=
    restrictIso (Over.mk p) C.ι (W.ι ≫ U.ι) ≪≫
      (Over.pullback C.ι).mapIso (restrictIso (Over.mk p) W.ι U.ι)
  let p₀ := pullback.snd p k
  have hkn : SmoothOfRelativeDimension n p₀ :=
    baseChangeProperty_of_overIso (@SmoothOfRelativeDimension.{u} n) ek hn
  have hkg : SmoothOfRelativeDimension g p₀ := by
    have htc : HasPointedAbelianPullback p₀ (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection _ _ hs k) g c :=
      (pointed_iterated hs k c).mpr (by simpa only [hk] using ht)
    obtain ⟨A₂, hd, ⟨e₂⟩⟩ :=
      (pointed_iff_overIso (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection_snd _ _ hs k) c).mp htc
    let : SmoothOfRelativeDimension g (pullback.snd p₀ c) :=
      baseChangeProperty_of_overIso (@SmoothOfRelativeDimension.{u} g) e₂.symm hd
    let : SmoothOfRelativeDimension n p₀ := hkn
    let : SmoothOfRelativeDimension n (pullback.snd p₀ c) := inferInstance
    let : Nonempty ↥(pullback p₀ c) :=
      ⟨Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection _ _ (Langlands.AlgebraicGeometry.SectionComponent.baseChangeSection_snd _ _ hs k) c (IsLocalRing.closedPoint K)⟩
    have dn := Langlands.GroupScheme.ReducedBaseSmooth.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      K _ (pullback.snd p₀ c) n
    have dg := Langlands.GroupScheme.ReducedBaseSmooth.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      K _ (pullback.snd p₀ c) g
    have hgn : n = g := by exact_mod_cast dn.symm.trans dg
    exact hgn ▸ hkn
  let : GeometricallyConnected p₀ :=
    baseChangeProperty_of_overIso @GeometricallyConnected ek ‹GeometricallyConnected r›
  obtain ⟨D, hD, hcD, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := c (IsLocalRing.closedPoint K)) (U := ⊤) (by trivial)
  let a := hD.fromSpec
  let v := IsOpenImmersion.lift a c (by
    rw [hD.range_fromSpec, range_fieldPoint, Set.singleton_subset_iff]
    exact hcD)
  have hv : v ≫ a = c := IsOpenImmersion.lift_fac ..
  let j := a ≫ k
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (a ≫ C.ι ≫ W.ι ≫ U.ι))
  refine ⟨Γ(C.toScheme, D), IsLocallyNoetherian.component_noetherian ⟨D, hD⟩, j, v, hj, ?_, ?_, ?_⟩
  · change v ≫ a ≫ k = t
    rw [← Category.assoc, hv, hk]
  · let : SmoothOfRelativeDimension g p₀ := hkg
    exact baseChangeProperty_of_overIso (@SmoothOfRelativeDimension.{u} g)
      (restrictIso (Over.mk p) a k)
      (inferInstanceAs (SmoothOfRelativeDimension g (pullback.snd p₀ a)))
  · exact baseChangeProperty_of_overIso @GeometricallyConnected (restrictIso (Over.mk p) a k)
      (inferInstanceAs (GeometricallyConnected (pullback.snd p₀ a)))

end Langlands.AbelianScheme.PointedProjectiveAbelianLocus
