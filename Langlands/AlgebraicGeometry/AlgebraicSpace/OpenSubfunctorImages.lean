import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Open subsheaves and images of etale morphisms -/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages

variable {S : Scheme.{u}} {F : Presheaf S} {A : Subfunctor F}

/-- Membership in a representable open subfunctor is local for the fppf
topology even if the ambient presheaf is not a sheaf. -/
theorem mem_of_coveringSieve (hA : IsOpenImmersion A.ι)
    {T : (Over S)ᵒᵖ} (x : F.obj T)
    (hx : A.sieveOfSection x ∈ fppfTopology S T.unop) :
    x ∈ A.obj T := by
  rw [GrothendieckTopology.mem_over_iff] at hx
  have hx' := Scheme.grothendieckTopology_monotone
    (P := @_root_.AlgebraicGeometry.Flat.{u} ⊓
      @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    (Q := ⊤) le_top T.unop.left hx
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology (P := ⊤) hx'
  let U (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.unop.hom)
  let f (i : 𝒰.I₀) : U i ⟶ T.unop := Over.homMk (𝒰.f i)
  apply OpenSubfunctorPoints.mem_of_jointly_surjective hA f ?_ x
  · intro i
    have hi := h𝒰 (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)
    rw [Sieve.overEquiv_iff] at hi
    exact hi
  · intro t
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq t
    exact ⟨i, z, hz⟩

/-- A representable open subfunctor of an fppf sheaf is an fppf sheaf. -/
theorem isSheaf_of_open
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    (hA : IsOpenImmersion A.ι) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) A.toFunctor := by
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type] at hF ⊢
  exact (A.isSheaf_iff hF).mpr (fun _ x hx => mem_of_coveringSieve hA x hx)

/-- Local closure of a subfunctor commutes with inverse image. -/
theorem sheafify_preimage {G : Presheaf S} (B : Subfunctor G) (g : F ⟶ G) :
    (B.preimage g).sheafify (fppfTopology S) =
      (B.sheafify (fppfTopology S)).preimage g := by
  ext T x
  change (B.preimage g).sieveOfSection x ∈ fppfTopology S T.unop ↔
    B.sieveOfSection (g.app T x) ∈ fppfTopology S T.unop
  have hs : (B.preimage g).sieveOfSection x =
      B.sieveOfSection (g.app T x) := by
    ext U f
    change g.app _ (F.map f.op x) ∈ B.obj _ ↔
      G.map f.op (g.app T x) ∈ B.obj _
    rw [g.naturality_apply]
  rw [hs]

/-- A locally surjective parametrization of an open chart has that chart
as its sheafified image. -/
theorem sheafify_range_comp {V W : Over S} (q : V ⟶ W)
    (b : (schemeYoneda S).obj W ⟶ F)
    (hq : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map q))
    (hb : IsOpenImmersion b) :
    (Subfunctor.range ((schemeYoneda S).map q ≫ b)).sheafify (fppfTopology S) =
      Subfunctor.range b := by
  apply le_antisymm
  · intro T x hx
    apply mem_of_coveringSieve (OpenSubfunctorLifting.range_open b hb) x
    apply (fppfTopology S).superset_covering ?_ hx
    intro U f hf
    obtain ⟨z, hz⟩ := hf
    exact ⟨((schemeYoneda S).map q).app _ z, hz⟩
  · rintro T x ⟨y, rfl⟩
    change _ ∈ fppfTopology S T.unop
    apply (fppfTopology S).superset_covering ?_ (hq.imageSieve_mem y)
    intro U f hf
    obtain ⟨z, hz⟩ := hf
    refine ⟨z, ?_⟩
    change b.app _ (((schemeYoneda S).map q).app _ z) =
      F.map f.op (b.app T y)
    rw [hz, b.naturality_apply]

/-- The topological image of an etale morphism, viewed as an open. -/
def schemeImageOpen {R T : Over S} (p : R ⟶ T) [Etale p.left] : T.left.Opens :=
  ⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩

/-- The actual open image scheme, with its structure map to the base. -/
def schemeImage {R T : Over S} (p : R ⟶ T) [Etale p.left] : Over S :=
  Over.mk ((schemeImageOpen p).ι ≫ T.hom)

/-- The inclusion of the image open into the target scheme. -/
def schemeImageι {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    schemeImage p ⟶ T :=
  Over.homMk (schemeImageOpen p).ι

instance schemeImageι_isOpenImmersion {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion (schemeImageι p).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (schemeImageOpen p).ι)

/-- Factorization of the original map through its open image. -/
def toSchemeImage {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    R ⟶ schemeImage p :=
  (OpenSubfunctorLifting.factors_through_open_iff (schemeImageι p) p).mpr (by
    change Set.range p.left ⊆ Set.range (schemeImageOpen p).ι
    rw [Scheme.Opens.range_ι]
    exact le_rfl) |>.choose

theorem toSchemeImage_fac {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    toSchemeImage p ≫ schemeImageι p = p :=
  (OpenSubfunctorLifting.factors_through_open_iff (schemeImageι p) p).mpr (by
    change Set.range p.left ⊆ Set.range (schemeImageOpen p).ι
    rw [Scheme.Opens.range_ι]
    exact le_rfl) |>.choose_spec

instance toSchemeImage_etale {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    Etale (toSchemeImage p).left := by
  have hcomp : (toSchemeImage p).left ≫ (schemeImageι p).left = p.left :=
    congrArg Over.Hom.left (toSchemeImage_fac p)
  have : Etale ((toSchemeImage p).left ≫ (schemeImageι p).left) := by
    rw [hcomp]
    infer_instance
  exact Etale.of_comp (toSchemeImage p).left (schemeImageι p).left

instance toSchemeImage_surjective {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    Surjective (toSchemeImage p).left := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨x, ?_⟩
  apply (schemeImageι p).left.isOpenEmbedding.injective
  have hcomp : (toSchemeImage p).left ≫ (schemeImageι p).left = p.left :=
    congrArg Over.Hom.left (toSchemeImage_fac p)
  change ((toSchemeImage p).left ≫ (schemeImageι p).left) x = y.val
  rw [hcomp]
  exact hx

/-- The fppf sheafified image of an etale scheme morphism is represented by
its actual open image. -/
theorem sheafify_range_schemeYoneda_map {R T : Over S} (p : R ⟶ T) [Etale p.left] :
    (Subfunctor.range ((schemeYoneda S).map p)).sheafify (fppfTopology S) =
      Subfunctor.range ((schemeYoneda S).map (schemeImageι p)) := by
  have hmap : (schemeYoneda S).map (toSchemeImage p) ≫
      (schemeYoneda S).map (schemeImageι p) = (schemeYoneda S).map p := by
    rw [← Functor.map_comp, toSchemeImage_fac]
  rw [← hmap]
  exact sheafify_range_comp _ _
    (isLocallySurjective_schemeYoneda_map (toSchemeImage p))
    (AffineOpenSubfunctors.isOpenImmersion_schemeYoneda_map _ inferInstance)

/-- The fppf sheafified image of a representable etale map is a
representable open subfunctor of its target. -/
theorem sheafify_range_open {G : Presheaf S} (a : G ⟶ F) (ha : IsEtale a) :
    IsOpenImmersion ((Subfunctor.range a).sheafify (fppfTopology S)).ι := by
  let Q := (Subfunctor.range a).sheafify (fppfTopology S)
  apply MorphismProperty.relative.of_exists
  intro T g
  let p := ha.representable.snd g
  have : Etale p.left := ha.projection g _ p (ha.representable.isPullback g)
  let i := schemeImageι p
  have : Mono i := Over.mono_of_mono_left i
  have hr : Subfunctor.range ((schemeYoneda S).map i) = Q.preimage g := by
    change Subfunctor.range ((schemeYoneda S).map (schemeImageι p)) =
      ((Subfunctor.range a).sheafify (fppfTopology S)).preimage g
    rw [← sheafify_preimage,
      ← OpenSubfunctorLifting.range_eq_preimage_of_isPullback
        (ha.representable.isPullback g)]
    exact (sheafify_range_schemeYoneda_map p).symm
  let b := (schemeYoneda S).map i ≫ g
  have hb : Subfunctor.range b ≤ Q := by
    rintro U x ⟨z, rfl⟩
    change ((schemeYoneda S).map i).app U z ∈ (Q.preimage g).obj U
    rw [← hr]
    exact ⟨z, rfl⟩
  let b' := Subfunctor.lift b hb
  refine ⟨schemeImage p, b', i, ?_, inferInstanceAs
    (_root_.AlgebraicGeometry.IsOpenImmersion (schemeImageι p).left)⟩
  exact OpenSubfunctorLifting.isPullback_subfunctor_of_range Q b'
    ((schemeYoneda S).map i) g (by simp [b', b]) hr

/-- The image of an etale map is a sheaf if the target is a sheaf. -/
theorem sheafify_range_isSheaf {G : Presheaf S} (a : G ⟶ F) (ha : IsEtale a)
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S)
      ((Subfunctor.range a).sheafify (fppfTopology S)).toFunctor :=
  isSheaf_of_open hF (sheafify_range_open a ha)

/-- Local surjectivity is stable under pullback for actual type-valued
presheaves. -/
theorem isLocallySurjective_of_isPullback {G H K : Presheaf S}
    {a : G ⟶ F} {b : H ⟶ G} {p : H ⟶ K} {g : K ⟶ F}
    (sq : IsPullback b p a g)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) p := by
  constructor
  intro T y
  apply (fppfTopology S).superset_covering ?_ (ha.imageSieve_mem (g.app _ y))
  intro U f hf
  obtain ⟨x, hx⟩ := hf
  have hx' : a.app _ x = g.app _ (K.map f.op y) :=
    hx.trans (g.naturality_apply f.op y).symm
  obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback (sq.app (op U)) x
    (K.map f.op y) hx'
  exact ⟨z, hz⟩

/-- An etale morphism of schemes which is locally surjective in the fppf
topology is surjective on underlying points. -/
theorem scheme_surjective_of_isLocallySurjective {R T : Over S} (p : R ⟶ T)
    [Etale p.left]
    (hp : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      ((schemeYoneda S).map p)) : Surjective p.left := by
  have htop := (CategoryTheory.Presheaf.isLocallySurjective_iff_range_sheafify_eq_top'
    (fppfTopology S) ((schemeYoneda S).map p)).mp hp
  have hi : ULift.up (𝟙 T) ∈
      (Subfunctor.range ((schemeYoneda S).map (schemeImageι p))).obj (op T) := by
    rw [← sheafify_range_schemeYoneda_map, htop]
    trivial
  obtain ⟨b, hb⟩ := hi
  have hb' : b.down ≫ schemeImageι p = 𝟙 T := congrArg ULift.down hb
  constructor
  intro t
  have ht : t ∈ Set.range (schemeImageι p).left :=
    ⟨b.down.left t, congrArg (fun f : T ⟶ T => f.left t) hb'⟩
  change t ∈ Set.range (schemeImageOpen p).ι at ht
  rw [Scheme.Opens.range_ι] at ht
  exact ht

/-- A locally surjective representable etale transformation is
geometrically surjective. -/
theorem isSurjective_of_isEtale_isLocallySurjective {G : Presheaf S}
    (a : G ⟶ F) (ha : IsEtale a)
    (hs : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a) :
    IsSurjective a := by
  let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u}) (Over.forget S)
  apply MorphismProperty.relative.of_exists
  intro T g
  have : Etale (ha.representable.snd g).left :=
    ha.projection g _ _ (ha.representable.isPullback g)
  exact ⟨_, _, _, ha.representable.isPullback g,
    scheme_surjective_of_isLocallySurjective _
      (isLocallySurjective_of_isPullback (ha.representable.isPullback g) hs)⟩

/-- The canonical factorization into the sheafified image is the base
change of the original map by the image inclusion. -/
theorem toRangeSheafify_isPullback {G : Presheaf S} (a : G ⟶ F) :
    IsPullback (𝟙 G) (Subfunctor.toRangeSheafify (fppfTopology S) a) a
      ((Subfunctor.range a).sheafify (fppfTopology S)).ι :=
  IsPullback.of_horiz_isIso_mono ⟨by
    ext T x
    rfl⟩

/-- The canonical atlas of the image of an etale map is etale. -/
theorem toRangeSheafify_isEtale {G : Presheaf S} (a : G ⟶ F) (ha : IsEtale a) :
    IsEtale (Subfunctor.toRangeSheafify (fppfTopology S) a) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) (toRangeSheafify_isPullback a) ha

/-- The canonical atlas of the image of an etale map is geometrically
surjective. -/
theorem toRangeSheafify_isSurjective {G : Presheaf S} (a : G ⟶ F) (ha : IsEtale a) :
    IsSurjective (Subfunctor.toRangeSheafify (fppfTopology S) a) :=
  isSurjective_of_isEtale_isLocallySurjective _
    (toRangeSheafify_isEtale a ha) inferInstance

/-- The diagonal square of a monomorphism is cartesian. -/
theorem diag_isPullback_of_mono
    {C : Type v} [Category.{w} C] [HasBinaryProducts C]
    {B D : C} (f : B ⟶ D) [Mono f] :
    IsPullback f (Limits.diag B) (Limits.diag D) (prod.map f f) := by
  apply IsPullback.of_isLimit' ⟨by apply prod.hom_ext <;> simp⟩
  refine PullbackCone.IsLimit.mk _
    (fun c => c.snd ≫ prod.fst) ?_ ?_ ?_
  · intro c
    have hc := congrArg (fun k => k ≫ prod.fst) c.condition
    simpa using hc.symm
  · intro c
    apply prod.hom_ext
    · simp
    · apply (cancel_mono f).mp
      have h1 := congrArg (fun k => k ≫ prod.fst) c.condition
      have h2 := congrArg (fun k => k ≫ prod.snd) c.condition
      simp only [Category.assoc, Limits.diag, prod.lift_fst, prod.lift_snd,
        prod.map_fst, prod.map_snd, Category.comp_id] at h1 h2
      simpa using h1.symm.trans h2
  · intro c m _ hm
    have hc := congrArg (fun k => k ≫ prod.fst) hm
    simpa using hc

/-- Every subfunctor inherits a closed-immersion diagonal from its
ambient presheaf. No sheaf or openness hypothesis is needed. -/
theorem isClosedImmersion_diag_subfunctor
    (hF : IsClosedImmersion (Limits.diag F)) (B : Subfunctor F) :
    IsClosedImmersion (Limits.diag B.toFunctor) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).relative
      (schemeYoneda S))
    (diag_isPullback_of_mono B.ι) hF

/-- The sheafified image of an etale scheme chart of a sheaf with closed
diagonal is an algebraic space. -/
theorem sheafify_range_isAlgebraicSpace {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a)
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    (hd : IsClosedImmersion (Limits.diag F)) :
    IsAlgebraicSpace S
      ⟨((Subfunctor.range a).sheafify (fppfTopology S)).toFunctor,
        sheafify_range_isSheaf a ha hF⟩ :=
  ⟨(isClosedImmersion_diag_subfunctor hd _).representable, U,
    Subfunctor.toRangeSheafify (fppfTopology S) a,
    toRangeSheafify_isEtale a ha, toRangeSheafify_isSurjective a ha⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
