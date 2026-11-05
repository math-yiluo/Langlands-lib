import Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry
import Langlands.AlgebraicGeometry.SectionComponentLocality

/-! # Specializing section-selected components over a DVR -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.SectionComponent

/-- The actual map of fibres induced by restricting the source to an open subscheme. -/
def openFiberMap {U X Y : Scheme.{u}} (j : U ⟶ X) (p : X ⟶ Y) (y : Y) :
    (j ≫ p).fiber y ⟶ p.fiber y :=
  pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem openFiberMap_fiberι {U X Y : Scheme.{u}} (j : U ⟶ X) (p : X ⟶ Y) (y : Y) :
    openFiberMap j p y ≫ p.fiberι y = (j ≫ p).fiberι y ≫ j :=
  pullback.lift_fst ..

instance {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (p : X ⟶ Y) (y : Y) :
    IsOpenImmersion (openFiberMap j p y) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (by infer_instance) (by infer_instance) rfl (by simp)

/-- Remove precisely the unselected part of a closed fibre. -/
def fiberClopenNeighbourhood {X Y : Scheme.{u}} (p : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y)) : X.Opens :=
  ⟨(p.fiberι y '' (C : Set (p.fiber y))ᶜ)ᶜ, by
    have hι : IsClosedEmbedding (p.fiberι y) :=
      ⟨(p.fiberι y).isEmbedding, by
        rw [Scheme.Hom.range_fiberι]
        exact hy.preimage p.continuous⟩
    exact (hι.isClosedMap _ C.isOpen.isClosed_compl).isOpen_compl⟩

@[simp]
theorem fiberι_mem_fiberClopenNeighbourhood {X Y : Scheme.{u}} (p : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y))
    (z : p.fiber y) :
    p.fiberι y z ∈ fiberClopenNeighbourhood p y hy C ↔ z ∈ C := by
  change p.fiberι y z ∉ p.fiberι y '' (C : Set (p.fiber y))ᶜ ↔ z ∈ C
  constructor
  · intro hz
    by_contra hn
    exact hz ⟨z, hn, rfl⟩
  · rintro hz ⟨w, hw, heq⟩
    exact hw ((p.fiberι y).isEmbedding.injective heq ▸ hz)

/-- The special fibre of the neighbourhood maps into the prescribed clopen. -/
theorem range_openFiberMap_neighbourhood {X Y : Scheme.{u}} (p : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y)) :
    Set.range (openFiberMap (fiberClopenNeighbourhood p y hy C).ι p y) ⊆
      Set.range (show (p.fiber y).Opens from C.toOpens).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  apply (fiberι_mem_fiberClopenNeighbourhood p y hy C _).mp
  rw [← Scheme.Hom.comp_apply, openFiberMap_fiberι, Scheme.Hom.comp_apply]
  exact (((fiberClopenNeighbourhood p y hy C).ι ≫ p).fiberι y z).property

/-- A reduced selected clopen gives a reduced actual fibre of its neighbourhood. -/
theorem isReduced_fiber_fiberClopenNeighbourhood {X Y : Scheme.{u}} (p : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y))
    [AlgebraicGeometry.IsReduced C.toOpens] :
    AlgebraicGeometry.IsReduced
      (((fiberClopenNeighbourhood p y hy C).ι ≫ p).fiber y) := by
  let k := IsOpenImmersion.lift (show (p.fiber y).Opens from C.toOpens).ι
    (openFiberMap (fiberClopenNeighbourhood p y hy C).ι p y)
    (range_openFiberMap_neighbourhood p y hy C)
  exact isReduced_of_isOpenImmersion k

/-- A section whose selected point belongs to the clopen factors through its neighbourhood. -/
theorem range_section_subset_fiberClopenNeighbourhood
    {X Y : Scheme.{u}} (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y))
    (hC : fiberPoint p e he y ∈ C) :
    Set.range e ⊆ Set.range (fiberClopenNeighbourhood p y hy C).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  change e t ∉ p.fiberι y '' (C : Set (p.fiber y))ᶜ
  rintro ⟨z, hz, heq⟩
  have ht : y = t := by
    calc
      y = p (p.fiberι y z) := (structure_fiberι p y z).symm
      _ = p (e t) := congrArg p heq
      _ = t := congrArg (fun f : Y ⟶ Y => f t) he
  subst t
  apply hz
  have hzpt : z = fiberPoint p e he y := by
    apply (p.fiberι y).isEmbedding.injective
    exact heq.trans (fiberι_fiberPoint p e he y).symm
  exact hzpt ▸ hC

/-- The chosen clopen in the closed fibre maps to its actual open neighbourhood. -/
def fiberClopenInclusion {X Y : Scheme.{u}} (p : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y)) :
    Scheme.Opens.toScheme (X := p.fiber y) C.toOpens ⟶
      Scheme.Opens.toScheme (fiberClopenNeighbourhood p y hy C) :=
  IsOpenImmersion.lift (fiberClopenNeighbourhood p y hy C).ι
    ((show (p.fiber y).Opens from C.toOpens).ι ≫ p.fiberι y) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact (fiberι_mem_fiberClopenNeighbourhood p y hy C z.val).mpr z.property)

@[reassoc (attr := simp)]
theorem fiberClopenInclusion_ι {X Y : Scheme.{u}} (p : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (C : Clopens (p.fiber y)) :
    fiberClopenInclusion p y hy C ≫ (fiberClopenNeighbourhood p y hy C).ι =
      (show (p.fiber y).Opens from C.toOpens).ι ≫ p.fiberι y :=
  IsOpenImmersion.lift_fac ..

/-- The image of a connected scheme lies in the open component through any image point. -/
theorem range_map_subset_connectedComponentOpen {S X : Scheme.{u}}
    [ConnectedSpace S] [IsLocallyNoetherian X] (g : S ⟶ X) (s : S) :
    Set.range g ⊆ Set.range (connectedComponentOpen X (g s)).ι := by
  rw [Scheme.Opens.range_ι]
  exact (isConnected_range g.continuous).subset_connectedComponent ⟨s, rfl⟩

/-- Two sections meeting a connected reduced clopen of the special fibre of a flat
DVR family meet the same connected component of the generic fibre. -/
theorem section_generic_mem_componentSet_of_clopen
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] [LocallyOfFinitePresentation p]
    (e v : Spec (CommRingCat.of R) ⟶ X)
    (he : e ≫ p = 𝟙 _) (hv : v ≫ p = 𝟙 _)
    (C : Clopens (p.fiber (IsLocalRing.closedPoint R)))
    [ConnectedSpace C.toOpens] [AlgebraicGeometry.IsReduced C.toOpens]
    (hCe : fiberPoint p e he (IsLocalRing.closedPoint R) ∈ C)
    (hCv : fiberPoint p v hv (IsLocalRing.closedPoint R) ∈ C) :
    v (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ componentSet p e he := by
  let s := IsLocalRing.closedPoint R
  have hs : IsClosed ({s} : Set (Spec (CommRingCat.of R))) :=
    (IsLocalRing.isClosed_singleton_closedPoint R)
  let U := fiberClopenNeighbourhood p s hs C
  let eU : Spec (CommRingCat.of R) ⟶ U := IsOpenImmersion.lift U.ι e
    (range_section_subset_fiberClopenNeighbourhood p e he s hs C hCe)
  let vU : Spec (CommRingCat.of R) ⟶ U := IsOpenImmersion.lift U.ι v
    (range_section_subset_fiberClopenNeighbourhood p v hv s hs C hCv)
  have heU : eU ≫ U.ι = e := IsOpenImmersion.lift_fac ..
  have hvU : vU ≫ U.ι = v := IsOpenImmersion.lift_fac ..
  let k := fiberClopenInclusion p s hs C
  have hek : eU s ∈ Set.range k := by
    refine ⟨⟨fiberPoint p e he s, hCe⟩, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, fiberClopenInclusion_ι]
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, fiberι_fiberPoint] using
      (congrArg (fun q : Spec (CommRingCat.of R) ⟶ X => q s) heU).symm
  have hvk : vU s ∈ Set.range k := by
    refine ⟨⟨fiberPoint p v hv s, hCv⟩, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, fiberClopenInclusion_ι]
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, fiberι_fiberPoint] using
      (congrArg (fun q : Spec (CommRingCat.of R) ⟶ X => q s) hvU).symm
  have hvconn : vU s ∈ connectedComponent (eU s) :=
    (isConnected_range k.continuous).subset_connectedComponent hek hvk
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let W := connectedComponentOpen U (eU s)
  let eW : Spec (CommRingCat.of R) ⟶ W := IsOpenImmersion.lift W.ι eU
    (range_map_subset_connectedComponentOpen eU s)
  have hvWrange : Set.range vU ⊆ Set.range W.ι := by
    have h := range_map_subset_connectedComponentOpen vU s
    rw [Scheme.Opens.range_ι] at h ⊢
    change Set.range vU ⊆ connectedComponent (eU s)
    rwa [connectedComponent_eq hvconn]
  let vW : Spec (CommRingCat.of R) ⟶ W := IsOpenImmersion.lift W.ι vU hvWrange
  let j : Scheme.Opens.toScheme W ⟶ X := W.ι ≫ U.ι
  let q := j ≫ p
  have heWj : eW ≫ j = e := by
    dsimp only [j]
    rw [← Category.assoc, IsOpenImmersion.lift_fac, heU]
  have hvWj : vW ≫ j = v := by
    dsimp only [j]
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hvU]
  have heW : eW ≫ q = 𝟙 _ := by rw [← Category.assoc, heWj, he]
  have hvW : vW ≫ q = 𝟙 _ := by rw [← Category.assoc, hvWj, hv]
  let : AlgebraicGeometry.IsReduced ((U.ι ≫ p).fiber s) :=
    isReduced_fiber_fiberClopenNeighbourhood p s hs C
  let : AlgebraicGeometry.IsReduced (q.fiber s) := by
    let a := openFiberMap W.ι (U.ι ≫ p) s
    have : AlgebraicGeometry.IsReduced ((W.ι ≫ (U.ι ≫ p)).fiber s) :=
      isReduced_of_isOpenImmersion a
    simpa only [q, j, Category.assoc] using this
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  let : PreconnectedSpace (q.fiber η) :=
    FlatReducedDvrConnectedness.preconnectedSpace_genericFiber_of_reduced_specialFiber R W q
  have hgeneric : vW η ∈ componentSet q eW heW := by
    refine ⟨η, fiberPoint q vW hvW η, ?_, fiberι_fiberPoint q vW hvW η⟩
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  have h := image_componentSet_subset (f := p) (e := e) (he := he)
    (f' := q) (e' := eW) (he' := heW) j (𝟙 _) (by simp [q]) (by simpa using heWj)
    ⟨vW η, hgeneric, rfl⟩
  simpa only [← Scheme.Hom.comp_apply, hvWj] using h

/-- The selected component of a locally finite-type residue fibre as a clopen. -/
def fiberComponentClopen {X Y : Scheme.{u}} (p : X ⟶ Y) [LocallyOfFiniteType p]
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 _) (y : Y) : Clopens (p.fiber y) :=
  ⟨connectedComponent (fiberPoint p e he y),
    isClosed_connectedComponent, (fiberComponentOpen p e he y).isOpen⟩

instance {X Y : Scheme.{u}} (p : X ⟶ Y) [LocallyOfFiniteType p]
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 _) (y : Y) :
    ConnectedSpace (fiberComponentClopen p e he y).toOpens :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- The selected reduced special-fibre component of a flat DVR family persists
along every second section through it. -/
theorem section_generic_mem_componentSet_of_closed
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] [LocallyOfFinitePresentation p]
    (e v : Spec (CommRingCat.of R) ⟶ X)
    (he : e ≫ p = 𝟙 _) (hv : v ≫ p = 𝟙 _)
    [AlgebraicGeometry.IsReduced (fiberComponentOpen p e he (IsLocalRing.closedPoint R))]
    (hclosed : v (IsLocalRing.closedPoint R) ∈ componentSet p e he) :
    v (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ componentSet p e he := by
  let C := fiberComponentClopen p e he (IsLocalRing.closedPoint R)
  have hCv : fiberPoint p v hv (IsLocalRing.closedPoint R) ∈ C := by
    apply (fiberι_mem_componentSet_iff p e he _ _).mp
    simpa only [fiberι_fiberPoint] using hclosed
  let : AlgebraicGeometry.IsReduced (Scheme.Opens.toScheme (X := p.fiber _) C.toOpens) := by
    change AlgebraicGeometry.IsReduced (fiberComponentOpen p e he (IsLocalRing.closedPoint R))
    infer_instance
  exact section_generic_mem_componentSet_of_clopen R p e v he hv C
    mem_connectedComponent hCv

end Langlands.AlgebraicGeometry.SectionComponent
