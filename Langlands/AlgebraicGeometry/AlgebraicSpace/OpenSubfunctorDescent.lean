import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorLifting
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry

/-! # Descent of invariant open subfunctors -/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorDescent

open OpenSubfunctorLifting

/-- An invariant subfunctor is recovered by pulling back its universal image. -/
theorem universalImage_preimage_eq_of_invariant
    {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ Type w}
    (π : F ⟶ G) (A : Subfunctor F)
    (hA : ∀ (T : Cᵒᵖ) (x y : F.obj T), π.app T x = π.app T y →
      (x ∈ A.obj T ↔ y ∈ A.obj T)) :
    (universalImage π A).preimage π = A := by
  apply le_antisymm (universalImage_preimage_le π A)
  intro T x hx T' f y hy
  apply (hA T' y (F.map f x) (hy.trans (π.naturality_apply f x).symm)).mpr
  exact A.map f hx

section Schemes

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {R T W U : Over S}

/-- Universal-image membership means that every point over the image lies in
the given open, including after arbitrary scheme base change. -/
theorem mem_universalImage_scheme_iff (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left] (f : U ⟶ T) :
    ULift.up f ∈ (universalImage ((schemeYoneda S).map p)
      (Subfunctor.range ((schemeYoneda S).map q))).obj (op U) ↔
      Set.range f.left ⊆ (p.left '' (Set.range q.left)ᶜ)ᶜ := by
  constructor
  · intro h _ hx
    obtain ⟨x, rfl⟩ := hx
    rintro ⟨r, hr, hpr⟩
    let D := Limits.pullback p f
    let a : D ⟶ R := Limits.pullback.fst p f
    let b : D ⟶ U := Limits.pullback.snd p f
    have ha := h (op D) b.op (ULift.up a)
      (show ULift.up (a ≫ p) = ULift.up (b ≫ f) from
        congrArg ULift.up Limits.pullback.condition)
    obtain ⟨⟨c⟩, hc⟩ := ha
    change ULift.up (c ≫ q) = ULift.up a at hc
    have hc' : c ≫ q = a := ULift.up_injective hc
    obtain ⟨z, hza, _⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback p f).map (Over.forget S)) r x hpr
    apply hr
    refine ⟨c.left z, ?_⟩
    exact (congrArg (fun k : D ⟶ R => k.left z) hc').trans hza
  · intro h D s x hx
    obtain ⟨b⟩ := x
    change ULift.up (b ≫ p) = ULift.up (s.unop ≫ f) at hx
    have hx' : b ≫ p = s.unop ≫ f := ULift.up_injective hx
    obtain ⟨c, hc⟩ := (factors_through_open_iff q b).mpr (by
      rintro _ ⟨z, rfl⟩
      by_contra hz
      apply h ⟨s.unop.left z, rfl⟩
      exact ⟨b.left z, hz, congrArg (fun k : D.unop ⟶ T => k.left z) hx'⟩)
    exact ⟨ULift.up c, congrArg ULift.up hc⟩

/-- The open of base points whose entire fibre lies in the given open. -/
def universalOpen (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left]
    (hp : IsClosedMap p.left) : T.left.Opens :=
  ⟨(p.left '' (Set.range q.left)ᶜ)ᶜ,
    (hp _ q.left.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩

/-- The actual open subscheme representing the universal image on a scheme test. -/
def universalScheme (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left]
    (hp : IsClosedMap p.left) : Over S :=
  Over.mk ((universalOpen p q hp).ι ≫ T.hom)

/-- Inclusion of the universal open into the test scheme. -/
def universalMap (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left]
    (hp : IsClosedMap p.left) : universalScheme p q hp ⟶ T :=
  Over.homMk (universalOpen p q hp).ι

instance (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left] (hp : IsClosedMap p.left) :
    _root_.AlgebraicGeometry.IsOpenImmersion (universalMap p q hp).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (universalOpen p q hp).ι)

/-- The geometric universal image is the range of the constructed open scheme. -/
theorem universalImage_scheme_eq_range (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left] (hp : IsClosedMap p.left) :
    universalImage ((schemeYoneda S).map p)
      (Subfunctor.range ((schemeYoneda S).map q)) =
      Subfunctor.range ((schemeYoneda S).map (universalMap p q hp)) := by
  ext D ⟨f⟩
  rw [mem_universalImage_scheme_iff,
    ← show Set.range (universalMap p q hp).left =
      (p.left '' (Set.range q.left)ᶜ)ᶜ from Scheme.Opens.range_ι (universalOpen p q hp),
    ← factors_through_open_iff (universalMap p q hp) f]
  change (∃ b : D.unop ⟶ universalScheme p q hp, b ≫ universalMap p q hp = f) ↔
    ∃ b : ULift (D.unop ⟶ universalScheme p q hp),
      ULift.up (b.down ≫ universalMap p q hp) = ULift.up f
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨ULift.up b, congrArg ULift.up hb⟩
  · rintro ⟨⟨b⟩, hb⟩
    exact ⟨b, ULift.up_injective hb⟩

end Schemes

section Relative

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {F G : Presheaf S}

/-- Universal images of open subfunctors are open if every represented
projection is a closed map on scheme points. -/
theorem universalImage_open_of_closed (π : F ⟶ G) (hπ : IsRepresentableMorphism π)
    (hclosed : ∀ ⦃T R : Over S⦄ (g : (schemeYoneda S).obj T ⟶ G)
      (a : (schemeYoneda S).obj R ⟶ F) (p : R ⟶ T),
      IsPullback a ((schemeYoneda S).map p) π g → IsClosedMap p.left)
    (A : Subfunctor F) (hA : IsOpenImmersion A.ι) :
    IsOpenImmersion (universalImage π A).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let R := hπ.pullback g
  let a := hπ.fst g
  let p : R ⟶ T := hπ.snd g
  let ha := hA.representable
  let W := ha.pullback a
  let q : W ⟶ R := ha.snd a
  let : _root_.AlgebraicGeometry.IsOpenImmersion q.left :=
    hA.projection a (ha.fst a) q (ha.isPullback a)
  let hp := hclosed g a p (hπ.isPullback g)
  have hq : Subfunctor.range ((schemeYoneda S).map q) = A.preimage a := by
    have he := range_eq_preimage_of_isPullback (ha.isPullback a)
    rwa [Subfunctor.range_ι] at he
  let l := universalMap p q hp
  have hl : Subfunctor.range ((schemeYoneda S).map l) =
      (universalImage π A).preimage g := by
    rw [← universalImage_scheme_eq_range p q hp, hq,
      ← universalImage_preimage_of_isPullback (hπ.isPullback g)]
  have hle : Subfunctor.range ((schemeYoneda S).map l ≫ g) ≤ universalImage π A := by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, hl]
  let b := Subfunctor.lift ((schemeYoneda S).map l ≫ g) hle
  have : Mono l := Over.mono_of_mono_left l
  refine ⟨universalScheme p q hp, b, l, ?_, ?_⟩
  · exact isPullback_subfunctor_of_range (universalImage π A) b
      ((schemeYoneda S).map l) g (Subfunctor.lift_ι _ hle) hl
  · exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion l.left)

/-- In particular, universal image along a representable finite morphism
preserves open subfunctors. -/
theorem universalImage_open_of_finite (π : F ⟶ G) (hπ : IsFinite π)
    (A : Subfunctor F) (hA : IsOpenImmersion A.ι) :
    IsOpenImmersion (universalImage π A).ι := by
  apply universalImage_open_of_closed π hπ.representable ?_ A hA
  intro T R g a p h
  let : _root_.AlgebraicGeometry.IsFinite p.left := hπ.projection g a p h
  exact p.left.isClosedMap

end Relative

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorDescent
