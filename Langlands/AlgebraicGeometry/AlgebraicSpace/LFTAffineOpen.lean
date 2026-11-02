import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers

/-! # Affine open subfunctors represented by schemes locally of finite type

An affine open subfunctor is *LFT-affine* if it is represented by an affine scheme locally of
finite type over the base. Since representing schemes are unique up to isomorphism, local
finite type of one representing scheme passes to all of them, and along any relatively locally
finitely typed map of represented functors. This is preserved by the constructions used in the
group-space argument: ranges, preimages under isomorphisms and under affine changes of the
represented factor, and finite intersections.
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}} {F G : Presheaf S}

local instance : (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u})
    (Over.forget S)).RespectsIso := by
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

/-- The relative local-finite-type property of presheaf maps. -/
abbrev RelLFT {F G : Presheaf S} (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u}) (Over.forget S)).relative
    (schemeYoneda S) f

/-- An affine open subfunctor represented by an affine scheme locally of finite type. -/
def IsLFTAffineOpen (A : Subfunctor F) : Prop :=
  IsOpenImmersion A.ι ∧ ∃ V : Over S, IsAffine V.left ∧ LocallyOfFiniteType V.hom ∧
    Nonempty ((schemeYoneda S).obj V ≅ A.toFunctor)

theorem IsLFTAffineOpen.isAffineOpen {A : Subfunctor F} (hA : IsLFTAffineOpen A) :
    IsAffineOpen A :=
  ⟨hA.1, by obtain ⟨V, hV, -, he⟩ := hA.2; exact ⟨V, hV, he⟩⟩

/-- A relatively locally finitely typed map between represented functors transfers local finite
type of the target scheme to the source scheme. -/
theorem locallyOfFiniteType_of_relLFT {V V' : Over S}
    (φ : (schemeYoneda S).obj V ⟶ (schemeYoneda S).obj V') (hφ : RelLFT φ)
    (hV' : LocallyOfFiniteType V'.hom) : LocallyOfFiniteType V.hom := by
  obtain ⟨g, rfl⟩ := (schemeYoneda S).map_surjective φ
  have hg : LocallyOfFiniteType g.left := MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u}) (Over.forget S)) hφ
  rw [← Over.w g]
  infer_instance

/-- Isomorphisms are relatively locally finitely typed. -/
theorem relLFT_of_isIso {F G : Presheaf S} (f : F ⟶ G) [IsIso f] : RelLFT f := by
  apply MorphismProperty.relative.of_exists
  intro T g
  refine ⟨T, g ≫ inv f, 𝟙 T, ?_, ?_⟩
  · apply IsPullback.of_vert_isIso
    exact ⟨by simp⟩
  · change LocallyOfFiniteType (𝟙 T : T ⟶ T).left
    rw [Over.id_left]
    infer_instance

/-- Relative open immersions are relatively locally finitely typed. -/
theorem relLFT_of_isOpenImmersion {F G : Presheaf S} {f : F ⟶ G} (hf : IsOpenImmersion f) :
    RelLFT f := by
  apply MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget S)) ?_ f hf
  intro U V p hp
  have : _root_.AlgebraicGeometry.IsOpenImmersion p.left := hp
  exact inferInstanceAs (LocallyOfFiniteType p.left)

theorem RelLFT.comp {F G H : Presheaf S} {f : F ⟶ G} {g : G ⟶ H} (hf : RelLFT f)
    (hg : RelLFT g) : RelLFT (f ≫ g) := by
  have h : MorphismProperty.IsMultiplicative (@LocallyOfFiniteType.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderComposition (@LocallyOfFiniteType.{u}) :=
    h.toIsStableUnderComposition
  have : (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u})
      (Over.forget S)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (P := @LocallyOfFiniteType.{u}) (Over.forget S)
  exact MorphismProperty.comp_mem _ f g hf hg

/-- The inclusion of a smaller open subfunctor is a relative open immersion. -/
theorem isOpenImmersion_homOfLe {B C : Subfunctor F} (h : B ≤ C) (hB : IsOpenImmersion B.ι) :
    IsOpenImmersion (Subfunctor.homOfLe h) := by
  have sq : IsPullback (𝟙 B.toFunctor) (Subfunctor.homOfLe h) B.ι C.ι := by
    apply isPullback_of_elements
    · intro T x
      rfl
    · intro T x y _ hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext this
    · intro T x y hxy
      exact ⟨x, rfl, Subtype.ext hxy⟩
  exact MorphismProperty.of_isPullback (P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)).relative (schemeYoneda S))
    sq hB

/-- The map from a preimage subfunctor is a base change of the original map. -/
theorem isPullback_fromPreimage (A : Subfunctor G) (f : F ⟶ G) :
    IsPullback (A.fromPreimage f) (A.preimage f).ι A.ι f := by
  apply isPullback_of_elements
  · intro T x
    rfl
  · intro T x y _ hxy
    exact Subtype.ext hxy
  · intro T a x hax
    exact ⟨⟨x, by
      change f.app T x ∈ A.obj T
      rw [← hax]
      exact a.2⟩, Subtype.ext hax.symm, rfl⟩

/-- A relatively locally finitely typed map restricts to preimage subfunctors. -/
theorem relLFT_fromPreimage (A : Subfunctor G) {f : F ⟶ G} (hf : RelLFT f) :
    RelLFT (A.fromPreimage f) :=
  MorphismProperty.of_isPullback (isPullback_fromPreimage A f).flip hf

/-- Transfer of LFT-affineness to an affine open with a relatively locally finitely typed map to
an LFT-affine open. -/
theorem IsLFTAffineOpen.of_relLFT {A : Subfunctor F} {B : Subfunctor G} (hA : IsAffineOpen A)
    (hB : IsLFTAffineOpen B) (φ : A.toFunctor ⟶ B.toFunctor) (hφ : RelLFT φ) :
    IsLFTAffineOpen A := by
  obtain ⟨hAo, V, hV, ⟨eV⟩⟩ := hA
  obtain ⟨-, V', -, hV', ⟨eV'⟩⟩ := hB
  refine ⟨hAo, V, hV, ?_, ⟨eV⟩⟩
  apply locallyOfFiniteType_of_relLFT (eV.hom ≫ φ ≫ eV'.inv) _ hV'
  exact (relLFT_of_isIso _).comp (hφ.comp (relLFT_of_isIso _))

/-- The range of an open immersion from an affine scheme locally of finite type. -/
theorem isLFTAffineOpen_range {V : Over S} [IsAffine V.left] (hV : LocallyOfFiniteType V.hom)
    (f : (schemeYoneda S).obj V ⟶ F) (hf : IsOpenImmersion f) :
    IsLFTAffineOpen (Subfunctor.range f) := by
  have : Mono f := SliceOpenGluing.open_mono hf
  exact ⟨OpenSubfunctorLifting.range_open f hf, V, inferInstance, hV,
    ⟨asIso (Subfunctor.toRange f)⟩⟩

/-- Preimages under isomorphisms preserve LFT-affineness. -/
theorem IsLFTAffineOpen.preimage_iso (e : F ≅ G) {A : Subfunctor G} (hA : IsLFTAffineOpen A) :
    IsLFTAffineOpen (A.preimage e.hom) := by
  refine IsLFTAffineOpen.of_relLFT (hA.isAffineOpen.preimage_iso e) hA (A.fromPreimage e.hom) ?_
  exact relLFT_fromPreimage A (relLFT_of_isIso e.hom)

/-- The Yoneda image of a scheme morphism locally of finite type is relatively locally finitely
typed. -/
theorem relLFT_schemeYoneda_map {V W : Over S} (p : V ⟶ W) (hp : LocallyOfFiniteType p.left) :
    RelLFT ((schemeYoneda S).map p) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨g, rfl⟩ := (schemeYoneda S).map_surjective g
  let h := IsPullback.of_hasPullback p g
  exact ⟨_, _, _, h.map (schemeYoneda S),
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType.{u}) (h.map (Over.forget S)) hp⟩

/-- Change of the represented factor along a morphism locally of finite type is relatively
locally finitely typed. -/
theorem relLFT_mapRight {Λ Λ' : Over S} (ρ : Λ' ⟶ Λ) (hρ : LocallyOfFiniteType ρ.left) :
    RelLFT (extProd.mapRight (F := F) ρ) :=
  MorphismProperty.of_isPullback (extProd.isPullback_mapRight ρ).flip
    (relLFT_schemeYoneda_map ρ hρ)

/-- Preimages under an affine, locally finitely typed change of the represented factor preserve
LFT-affineness. -/
theorem IsLFTAffineOpen.preimage_mapRight {Λ Λ' : Over S} (ρ : Λ' ⟶ Λ) [IsAffineHom ρ.left]
    [LocallyOfFiniteType ρ.left] {A : Subfunctor (extProd F Λ)} (hA : IsLFTAffineOpen A) :
    IsLFTAffineOpen (A.preimage (extProd.mapRight ρ)) :=
  IsLFTAffineOpen.of_relLFT (hA.isAffineOpen.preimage_mapRight ρ) hA _
    (relLFT_fromPreimage A (relLFT_mapRight ρ inferInstance))

/-- A nonempty finite intersection of LFT-affine opens is LFT-affine. -/
theorem isLFTAffineOpen_iInf [IsAffine S] (hF : IsClosedImmersion (Limits.diag F))
    {I : Type v} [Finite I] (i₀ : I) (A : I → Subfunctor F) (hA : ∀ i, IsLFTAffineOpen (A i)) :
    IsLFTAffineOpen (⨅ i, A i) := by
  have : Nonempty I := ⟨i₀⟩
  have hI := isAffineOpen_iInf hF A (fun i ↦ (hA i).isAffineOpen)
  refine IsLFTAffineOpen.of_relLFT hI (hA i₀) (Subfunctor.homOfLe (iInf_le A i₀)) ?_
  exact relLFT_of_isOpenImmersion (isOpenImmersion_homOfLe _ hI.1)

/-- Finite intersections of preimages of an LFT-affine open under automorphisms. -/
theorem IsLFTAffineOpen.iInf_preimage_iso [IsAffine S] (hF : IsClosedImmersion (Limits.diag F))
    {I : Type v} [Finite I] (i₀ : I) (e : I → (F ≅ F)) {A : Subfunctor F}
    (hA : IsLFTAffineOpen A) :
    IsLFTAffineOpen (⨅ i, A.preimage (e i).hom) :=
  isLFTAffineOpen_iInf hF i₀ _ (fun i ↦ hA.preimage_iso (e i))

end Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors
