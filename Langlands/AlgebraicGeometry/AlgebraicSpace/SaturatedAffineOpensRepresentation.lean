import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImagePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineUniversalNeighborhoods
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointLiftedOpenCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentProof

/-! # AF representability from saturated affine opens of a finite cover -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SaturatedAffineOpensRepresentation

open OpenSubfunctorLifting OpenSubfunctorDescent FiniteAffineUniversalNeighborhoods
  OpenSubspaceGeometry

variable {S : Scheme.{u}} {W : Over S} {Y : AlgebraicSpace S}

/-- Every finite source point set has an affine open neighborhood saturated
under equality of images in the target presheaf. -/
def HasSaturatedAffineNeighborhoods
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf) : Prop :=
  ∀ F : Set W.left, F.Finite →
    ∃ V : W.left.Opens, IsAffineOpen V ∧ F ⊆ V ∧
      ∀ w w', SameImage g w w' → w ∈ V → w' ∈ V

private lemma mem_range_open_iff {D Q : Over S} (j : Q ⟶ W)
    [_root_.AlgebraicGeometry.IsOpenImmersion j.left] (a : D ⟶ W) :
    ULift.up a ∈ (Subfunctor.range ((schemeYoneda S).map j)).obj (op D) ↔
      Set.range a.left ⊆ Set.range j.left := by
  rw [← factors_through_open_iff j a]
  constructor
  · rintro ⟨⟨c⟩, hc⟩
    exact ⟨c, ULift.up_injective hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨ULift.up c, congrArg ULift.up hc⟩

/-- A point-saturated source open is the full inverse image of its universal image. -/
theorem universalAffineOpen_preimage
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf) (V : W.left.affineOpens)
    (hV : ∀ w w', SameImage g w w' → w ∈ V.val → w' ∈ V.val) :
    (universalAffineOpen g V).preimage g =
      Subfunctor.range ((schemeYoneda S).map (affineOpenInclusion V)) := by
  apply universalImage_preimage_eq_of_invariant
  rintro T ⟨a⟩ ⟨b⟩ hab
  have hab' : (schemeYoneda S).map a ≫ g = (schemeYoneda S).map b ≫ g := by
    apply uliftYonedaEquiv.injective
    simpa only [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map] using hab
  rw [mem_range_open_iff, mem_range_open_iff]
  change (Set.range a.left ⊆ Set.range V.val.ι) ↔
    (Set.range b.left ⊆ Set.range V.val.ι)
  rw [Scheme.Opens.range_ι]
  constructor
  · intro ha z hz
    obtain ⟨t, rfl⟩ := hz
    exact hV _ _ ⟨T.unop, a, b, t, hab', rfl, rfl⟩ (ha ⟨t, rfl⟩)
  · intro hb z hz
    obtain ⟨t, rfl⟩ := hz
    exact hV _ _ ⟨T.unop, b, a, t, hab'.symm, rfl, rfl⟩ (hb ⟨t, rfl⟩)

/-- The universal image of a saturated affine open is represented by an affine scheme. -/
theorem universalAffineOpen_isAffine
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf)
    (hg : IsFinite g) (hs : IsSurjective g) (V : W.left.affineOpens)
    (hV : ∀ w w', SameImage g w w' → w ∈ V.val → w' ∈ V.val) :
    ∃ P : Over S, IsAffine P.left ∧
      Nonempty ((schemeYoneda S).obj P ≅ (universalAffineOpen g V).toFunctor) := by
  let A := universalAffineOpen g V
  have hA : IsOpenImmersion A.ι := universalAffineOpen_isOpenImmersion hg V
  let j := affineOpenInclusion V
  have hpre : A.preimage g = Subfunctor.range ((schemeYoneda S).map j) :=
    universalAffineOpen_preimage g V hV
  have hle : Subfunctor.range ((schemeYoneda S).map j ≫ g) ≤ A := by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, hpre]
  let b := Subfunctor.lift ((schemeYoneda S).map j ≫ g) hle
  let : Mono j := Over.mono_of_mono_left j
  have sq : IsPullback b ((schemeYoneda S).map j) A.ι g :=
    isPullback_subfunctor_of_range A b ((schemeYoneda S).map j) g
      (Subfunctor.lift_ι _ _) hpre.symm
  have hbfin : IsFinite b := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget S)).relative (schemeYoneda S)) sq.flip hg
  have hbsurj : IsSurjective b := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).relative (schemeYoneda S)) sq.flip hs
  let : IsAffine (affineOpenTest V).left := V.property
  exact finiteSurjectiveAffineDescent S ((schemeToSpace S).obj (affineOpenTest V))
    (openSubspace Y A hA) (homMk b) hbfin hbsurj
    (schemeToSpace_isRepresentedByAffineScheme (affineOpenTest V))

/-- Saturated affine neighborhoods in the source supply open scheme charts
around every point of any scheme test. -/
theorem point_lifted_open_charts
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf)
    (hg : IsFinite g) (hs : IsSurjective g)
    (hClaim : HasSaturatedAffineNeighborhoods g)
    {T : Over S} (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    HasPointLiftedOpenCharts a := by
  intro x
  let p := OpenSubfunctorPoints.residueFieldPoint T x
  let a₀ := (schemeYoneda S).map p ≫ a
  obtain ⟨V₀, hV₀, hFV, hVsat⟩ := hClaim _
    (finite_sourceProjection_range hg (T.left.residueField x)
      (T.left.fromSpecResidueField x ≫ T.hom) a₀)
  let V : W.left.affineOpens := ⟨V₀, hV₀⟩
  let A := universalAffineOpen g V
  have hA : IsOpenImmersion A.ι := universalAffineOpen_isOpenImmersion hg V
  have hxV : uliftYonedaEquiv a₀ ∈
      A.obj (op (OpenSubfunctorPoints.residueFieldTest T x)) := by
    apply mem_universalImage_of_range_subset a₀ (sourceProjection hg a₀)
      (testProjection hg a₀) (sourceOverTest_square hg a₀) (affineOpenInclusion V)
    change Set.range (sourceProjection hg a₀).left ⊆ Set.range V₀.ι
    rw [Scheme.Opens.range_ι]
    exact hFV
  have hrange : Set.range p.left ⊆ Set.range (hA.rep.snd a).left := by
    apply (OpenSubfunctorPoints.mem_app_iff_range_subset hA a p).mp
    change uliftYonedaEquiv ((schemeYoneda S).map p ≫ a) ∈ _ at hxV
    simpa only [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map] using hxV
  have hxrange : x ∈ Set.range (hA.rep.snd a).left := by
    apply hrange
    exact ⟨(default : Spec (T.left.residueField x)),
      T.left.fromSpecResidueField_apply x _⟩
  obtain ⟨d, hd⟩ := hxrange
  obtain ⟨M, _, ⟨e⟩⟩ := universalAffineOpen_isAffine g hg hs V hVsat
  let c : hA.rep.pullback a ⟶ M :=
    (schemeYoneda S).preimage (hA.rep.fst a ≫ e.inv)
  have hc : (schemeYoneda S).map c ≫ e.hom = hA.rep.fst a := by
    dsimp [c]
    rw [Functor.map_preimage]
    simp
  refine ⟨M, hA.rep.pullback a, e.hom ≫ A.ι, hA.rep.snd a, c, d,
    IsOpenImmersion.iso_comp e hA, ?_, hd⟩
  rw [← Category.assoc, hc]
  exact (hA.rep.isPullback a).w.symm

/-- Saturated affine neighborhoods of finite source point sets imply
scheme representability of the entire target presheaf. -/
theorem exists_representation
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf)
    (hg : IsFinite g) (hs : IsSurjective g)
    (hClaim : HasSaturatedAffineNeighborhoods g) :
    ∃ P : Over S, Nonempty ((schemeYoneda S).obj P ≅ Y.presheaf) := by
  obtain ⟨T, a, _, ha, has⟩ := Y.exists_atlas
  exact exists_representation_of_point_lifted_open_charts Y.toSheaf a ha has
    (point_lifted_open_charts g hg hs hClaim a)

/-- Every scheme representative has AF when finite source point sets
admit saturated affine neighborhoods. -/
theorem hasFiniteAffineNeighborhoods_of_representation
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf)
    (hg : IsFinite g) (hs : IsSurjective g)
    (hClaim : HasSaturatedAffineNeighborhoods g)
    {P : Over S} (e : (schemeYoneda S).obj P ≅ Y.presheaf) :
    PointTopology.HasFiniteAffineNeighborhoods P.left := by
  let f : W ⟶ P := (schemeYoneda S).preimage (g ≫ e.inv)
  have hf : (schemeYoneda S).map f = g ≫ e.inv := Functor.map_preimage _ _
  have hfe : (schemeYoneda S).map f ≫ e.hom = g := by
    rw [hf]
    simp
  have hfr : IsFinite ((schemeYoneda S).map f) := by
    rw [hf]
    exact (MorphismProperty.cancel_right_of_respectsIso
      ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget S)).relative (schemeYoneda S)) g e.inv).mpr hg
  have hfs : IsSurjective ((schemeYoneda S).map f) := by
    rw [hf]
    exact (MorphismProperty.cancel_right_of_respectsIso
      ((MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).relative (schemeYoneda S)) g e.inv).mpr hs
  let : _root_.AlgebraicGeometry.IsFinite f.left :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget S)) (F := schemeYoneda S) hfr
  intro E hE
  obtain ⟨V₀, hV₀, hEV, hVsat⟩ := hClaim _ (f.left.finite_preimage hE)
  let V : W.left.affineOpens := ⟨V₀, hV₀⟩
  have hVsat' : ∀ w w', SameImage ((schemeYoneda S).map f) w w' →
      w ∈ V.val → w' ∈ V.val := by
    rintro w w' ⟨T, a, b, t, hab, hat, hbt⟩ hw
    apply hVsat w w' ?_ hw
    refine ⟨T, a, b, t, ?_, hat, hbt⟩
    have heq := congrArg (fun k => k ≫ e.hom) hab
    simpa only [Category.assoc, hfe] using heq
  obtain ⟨M, hM, ⟨eM⟩⟩ := universalAffineOpen_isAffine
    (Y := (schemeToSpace S).obj P) ((schemeYoneda S).map f) hfr hfs V hVsat'
  let Q := universalScheme f (affineOpenInclusion V) f.left.isClosedMap
  let i : Q ⟶ P := universalMap f (affineOpenInclusion V) f.left.isClosedMap
  have hrange : universalAffineOpen ((schemeYoneda S).map f) V =
      Subfunctor.range ((schemeYoneda S).map i) :=
    universalImage_scheme_eq_range f (affineOpenInclusion V) f.left.isClosedMap
  let : Mono i := Over.mono_of_mono_left i
  let eQ : (schemeYoneda S).obj Q ≅
      (universalAffineOpen ((schemeYoneda S).map f) V).toFunctor := by
    rw [hrange]
    exact asIso (Subfunctor.toRange ((schemeYoneda S).map i))
  let qIso : Q ≅ M := (schemeYoneda S).preimageIso (eQ ≪≫ eM.symm)
  let : IsIso qIso.hom.left := by
    change IsIso ((Over.forget S).map qIso.hom)
    infer_instance
  let : IsAffine M.left := hM
  have hQ : IsAffine Q.left := IsAffine.of_isIso qIso.hom.left
  refine ⟨⟨universalOpen f (affineOpenInclusion V) f.left.isClosedMap, hQ⟩, ?_⟩
  intro x hx
  change x ∉ f.left '' (Set.range (affineOpenInclusion V).left)ᶜ
  rintro ⟨z, hz, hzx⟩
  apply hz
  change z ∈ Set.range V₀.ι
  rw [Scheme.Opens.range_ι]
  apply hEV
  change f.left z ∈ E
  rwa [hzx]

/-- A finite surjective scheme cover with saturated affine neighborhoods
of every finite source point set has an AF scheme target. -/
theorem exists_AF_representation_of_saturated_affine_opens
    (g : (schemeYoneda S).obj W ⟶ Y.presheaf)
    (hg : IsFinite g) (hs : IsSurjective g)
    (hClaim : HasSaturatedAffineNeighborhoods g) :
    ∃ P : Over S, PointTopology.HasFiniteAffineNeighborhoods P.left ∧
      Nonempty ((schemeYoneda S).obj P ≅ Y.presheaf) := by
  obtain ⟨P, ⟨e⟩⟩ := exists_representation g hg hs hClaim
  exact ⟨P, hasFiniteAffineNeighborhoods_of_representation g hg hs hClaim e, ⟨e⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.SaturatedAffineOpensRepresentation
