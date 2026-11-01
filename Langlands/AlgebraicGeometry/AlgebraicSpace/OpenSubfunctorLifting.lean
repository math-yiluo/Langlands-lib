import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenFamilyLiftingStatement
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Open-family lifting across arbitrary thickenings

The right adjoint to inverse image constructs actual open algebraic subspaces.
Represented scheme tests and transported open covers prove the family coverage.
The concluding theorem proves the published family-lifting proposition.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorLifting

section Presheaves

variable {C : Type u} [Category.{v} C]
variable {F G : Cᵒᵖ ⥤ Type w}

/-- The largest subfunctor of `G` whose inverse image along `i` lies in `A`. -/
def universalImage (i : F ⟶ G) (A : Subfunctor F) : Subfunctor G where
  obj T := { y | ∀ (T' : Cᵒᵖ) (f : T ⟶ T') (x : F.obj T'),
    i.app T' x = G.map f y → x ∈ A.obj T' }
  map f y hy T' g x hx := hy T' (f ≫ g) x (by simpa using hx)

lemma universalImage_le_iff (i : F ⟶ G) (A : Subfunctor F) (B : Subfunctor G) :
    B ≤ universalImage i A ↔ B.preimage i ≤ A := by
  constructor
  · intro h T x hx
    exact h T hx T (𝟙 T) x (by simp)
  · intro h T y hy T' f x hx
    apply h T'
    change i.app T' x ∈ B.obj T'
    rw [hx]
    exact B.map f hy

lemma universalImage_preimage_le (i : F ⟶ G) (A : Subfunctor F) :
    (universalImage i A).preimage i ≤ A :=
  (universalImage_le_iff i A _).mp le_rfl

lemma universalImage_preimage_eq (i : F ⟶ G) [Mono i] (A : Subfunctor F) :
    (universalImage i A).preimage i = A := by
  apply le_antisymm (universalImage_preimage_le i A)
  intro T x hx T' f x' hx'
  have he : x' = F.map f x := by
    apply (CategoryTheory.mono_iff_injective (i.app T')).mp inferInstance
    exact hx'.trans (i.naturality_apply f x).symm
  rw [he]
  exact A.map f hx

/-- Universal image commutes with a genuine pullback square. -/
lemma universalImage_preimage_of_isPullback {H K : Cᵒᵖ ⥤ Type w}
    {i : F ⟶ G} {a : H ⟶ F} {p : H ⟶ K} {g : K ⟶ G}
    (sq : IsPullback a p i g) (A : Subfunctor F) :
    (universalImage i A).preimage g = universalImage p (A.preimage a) := by
  apply le_antisymm
  · intro T y hy T' f z hz
    apply hy T' f (a.app T' z)
    have hw := ConcreteCategory.congr_hom (NatTrans.congr_app sq.w T') z
    change i.app T' (a.app T' z) = g.app T' (p.app T' z) at hw
    rw [hw, hz, g.naturality_apply]
  · intro T y hy T' f x hx
    have hx' : i.app T' x = g.app T' (K.map f y) :=
      hx.trans (g.naturality_apply f y).symm
    obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback
      (sq.map ((evaluation Cᵒᵖ (Type w)).obj T')) x (K.map f y) hx'
    change a.app T' z = x at hz₁
    change p.app T' z = K.map f y at hz₂
    have hz := hy T' f z hz₂
    change a.app T' z ∈ A.obj T' at hz
    rwa [hz₁] at hz

/-- The image of a pullback projection is the inverse image of the other image. -/
lemma range_eq_preimage_of_isPullback {H K : Cᵒᵖ ⥤ Type w}
    {i : F ⟶ G} {a : H ⟶ F} {p : H ⟶ K} {g : K ⟶ G}
    (sq : IsPullback a p i g) :
    Subfunctor.range p = (Subfunctor.range i).preimage g := by
  ext T x
  exact Set.ext_iff.mp (Types.range_snd_of_isPullback (sq.app T)) x

/-- A square into a subfunctor is a pullback when its mono has the prescribed range. -/
lemma isPullback_subfunctor_of_range {H K : Cᵒᵖ ⥤ Type w}
    (B : Subfunctor G) (a : H ⟶ B.toFunctor) (p : H ⟶ K) (g : K ⟶ G)
    [Mono p] (hw : a ≫ B.ι = p ≫ g)
    (hr : Subfunctor.range p = B.preimage g) :
    IsPullback a p B.ι g := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app hw T, ?_, ?_⟩
  · intro x y h
    exact (CategoryTheory.mono_iff_injective (p.app T)).mp inferInstance h.2
  · intro x y hxy
    have hy : y ∈ (Subfunctor.range p).obj T := by
      rw [hr]
      change g.app T y ∈ B.obj T
      rw [← hxy]
      exact x.property
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_, hz⟩
    apply Subtype.ext
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hw T) z
    change (a.app T z).val = g.app T (p.app T z) at he
    rw [he, hz]
    exact hxy.symm

/-- A universal image of a subsheaf along a morphism of sheaves is again a sheaf. -/
theorem universalImage_isSheaf (J : GrothendieckTopology C) (i : F ⟶ G)
    (A : Subfunctor F) (hF : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G)
    (hA : Presieve.IsSheaf J A.toFunctor) :
    Presieve.IsSheaf J (universalImage i A).toFunctor := by
  apply ((universalImage i A).isSheaf_iff hG).mpr
  intro T y hy T' f x hx
  apply (A.isSheaf_iff hF).mp hA T' x
  apply J.superset_covering ?_ (J.pullback_stable f.unop hy)
  intro V g hg
  apply universalImage_preimage_le i A (op V)
  change i.app (op V) (F.map g.op x) ∈ (universalImage i A).obj (op V)
  rw [i.naturality_apply, hx]
  simpa using hg

end Presheaves

section Schemes

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {R T W U : Over S}

/-- The unique factorization criterion for an open immersion, with its base map. -/
lemma factors_through_open_iff (q : W ⟶ T)
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left] (f : U ⟶ T) :
    (∃ b : U ⟶ W, b ≫ q = f) ↔ Set.range f.left ⊆ Set.range q.left := by
  constructor
  · rintro ⟨b, rfl⟩ _ ⟨x, rfl⟩
    exact ⟨b.left x, rfl⟩
  · intro h
    let b := _root_.AlgebraicGeometry.IsOpenImmersion.lift q.left f.left h
    have hb : b ≫ q.left = f.left :=
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac q.left f.left h
    refine ⟨Over.homMk b ?_, ?_⟩
    · rw [← Over.w q, ← Category.assoc, hb]
      exact Over.w f
    · exact Over.OverMorphism.ext hb

/-- Universal image on represented schemes is detected by the topological open image. -/
lemma mem_universalImage_scheme (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsClosedImmersion p.left]
    [_root_.AlgebraicGeometry.Surjective p.left]
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left] (f : U ⟶ T) :
    ULift.up f ∈ (universalImage ((schemeYoneda S).map p)
      (Subfunctor.range ((schemeYoneda S).map q))).obj (op U) ↔
      Set.range f.left ⊆ p.left '' Set.range q.left := by
  constructor
  · rintro h _ ⟨x, rfl⟩
    let D := Limits.pullback p f
    let r : D ⟶ R := Limits.pullback.fst p f
    let s : D ⟶ U := Limits.pullback.snd p f
    have hs : _root_.AlgebraicGeometry.Surjective s.left :=
      MorphismProperty.of_isPullback
        (P := @_root_.AlgebraicGeometry.Surjective.{u})
        ((IsPullback.of_hasPullback p f).map (Over.forget S))
        (inferInstanceAs (_root_.AlgebraicGeometry.Surjective p.left))
    have hr := h (op D) s.op (ULift.up r)
      (show ULift.up (r ≫ p) = ULift.up (s ≫ f) from
        congrArg ULift.up Limits.pullback.condition)
    obtain ⟨⟨b⟩, hb⟩ := hr
    change ULift.up (b ≫ q) = ULift.up r at hb
    have hb' : b ≫ q = r := ULift.up_injective hb
    let := hs
    obtain ⟨z, hz⟩ := s.left.surjective x
    refine ⟨r.left z, ⟨b.left z, ?_⟩, ?_⟩
    · exact congrArg (fun k : D ⟶ R ↦ k.left z) hb'
    · have hw := congrArg (fun k : D ⟶ T ↦ k.left z)
        (show r ≫ p = s ≫ f from Limits.pullback.condition)
      simpa [hz] using hw
  · intro h D s x hx
    obtain ⟨b⟩ := x
    change ULift.up (b ≫ p) = ULift.up (s.unop ≫ f) at hx
    have hx' : b ≫ p = s.unop ≫ f := ULift.up_injective hx
    obtain ⟨c, hc⟩ := (factors_through_open_iff q b).mpr (by
      rintro _ ⟨z, rfl⟩
      have he := congrArg (fun k : D.unop ⟶ T ↦ k.left z) hx'
      obtain ⟨r, hr, hp⟩ := h ⟨s.unop.left z, rfl⟩
      have hbr : b.left z = r := p.left.isClosedEmbedding.injective (he.trans hp.symm)
      rwa [hbr])
    exact ⟨ULift.up c, congrArg ULift.up hc⟩

variable (p : R ⟶ T) (q : W ⟶ R)
    [_root_.AlgebraicGeometry.IsClosedImmersion p.left]
    [_root_.AlgebraicGeometry.Surjective p.left]
    [_root_.AlgebraicGeometry.IsOpenImmersion q.left]

/-- The open image transported across the underlying homeomorphism of a thickening. -/
def liftedOpen : T.left.Opens :=
  ⟨p.left '' Set.range q.left,
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨p.left.isClosedEmbedding.isEmbedding, p.left.surjective⟩).isOpenMap _
      q.left.isOpenEmbedding.isOpen_range⟩

/-- The actual representing open scheme, with its map to the original base. -/
def liftedScheme : Over S := Over.mk ((liftedOpen p q).ι ≫ T.hom)

def liftedMap : liftedScheme p q ⟶ T := Over.homMk (liftedOpen p q).ι

instance : _root_.AlgebraicGeometry.IsOpenImmersion (liftedMap p q).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (liftedOpen p q).ι)

lemma range_liftedMap :
    Set.range (liftedMap p q).left = p.left '' Set.range q.left :=
  Scheme.Opens.range_ι (liftedOpen p q)

/-- The geometric universal image is represented by the constructed open subscheme. -/
lemma universalImage_scheme_eq_range :
    universalImage ((schemeYoneda S).map p)
      (Subfunctor.range ((schemeYoneda S).map q)) =
      Subfunctor.range ((schemeYoneda S).map (liftedMap p q)) := by
  ext D ⟨f⟩
  rw [mem_universalImage_scheme, ← range_liftedMap p q,
    ← factors_through_open_iff (liftedMap p q) f]
  change (∃ b : D.unop ⟶ liftedScheme p q, b ≫ liftedMap p q = f) ↔
    ∃ b : ULift (D.unop ⟶ liftedScheme p q),
      ULift.up (b.down ≫ liftedMap p q) = ULift.up f
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨ULift.up b, congrArg ULift.up hb⟩
  · rintro ⟨⟨b⟩, hb⟩
    exact ⟨b, ULift.up_injective hb⟩

end Schemes

section Relative

open _root_.AlgebraicGeometry

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}} {F G : Presheaf S}

abbrev openMorphism : MorphismProperty (Presheaf S) :=
  @Langlands.AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion S

local instance : (@openMorphism S).RespectsIso := by
  change ((SliceOpenGluing.openProperty S).relative (schemeYoneda S)).RespectsIso
  infer_instance

/-- The universal image of an open subfunctor under an arbitrary thickening is open. -/
theorem universalImage_open (i : F ⟶ G) (hi : IsThickening i)
    (A : Subfunctor F) (hA : openMorphism A.ι) :
    openMorphism (universalImage i A).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let hr := hi.closedImmersion.representable
  let R := hr.pullback g
  let a := hr.fst g
  let p : R ⟶ T := hr.snd g
  let ha := hA.rep
  let W := ha.pullback a
  let q : W ⟶ R := ha.snd a
  let : _root_.AlgebraicGeometry.IsClosedImmersion p.left :=
    hi.closedImmersion.projection g a p (hr.isPullback g)
  let : _root_.AlgebraicGeometry.Surjective p.left :=
    hi.surjective.projection g a p (hr.isPullback g)
  let : _root_.AlgebraicGeometry.IsOpenImmersion q.left :=
    hA.property a (ha.fst a) q (ha.isPullback a)
  have hq : Subfunctor.range ((schemeYoneda S).map q) = A.preimage a := by
    have he := range_eq_preimage_of_isPullback (ha.isPullback a)
    rwa [Subfunctor.range_ι] at he
  let l := liftedMap p q
  have hl : Subfunctor.range ((schemeYoneda S).map l) =
      (universalImage i A).preimage g := by
    rw [← universalImage_scheme_eq_range p q, hq,
      ← universalImage_preimage_of_isPullback (hr.isPullback g)]
  have hle : Subfunctor.range ((schemeYoneda S).map l ≫ g) ≤ universalImage i A := by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, hl]
  let b := Subfunctor.lift ((schemeYoneda S).map l ≫ g) hle
  have : Mono l := Over.mono_of_mono_left l
  refine ⟨liftedScheme p q, b, l, ?_, ?_⟩
  · exact isPullback_subfunctor_of_range (universalImage i A) b
      ((schemeYoneda S).map l) g (Subfunctor.lift_ι _ hle) hl
  · exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion l.left)

/-- An unrestricted thickening is a monomorphism of the actual presheaves. -/
lemma thickening_mono (i : F ⟶ G) (hi : IsThickening i) : Mono i := by
  apply SliceOpenGluing.relative_monomorphisms_le_monomorphisms
  apply MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)) ?_ i hi.closedImmersion
  intro U V f hf
  let : _root_.AlgebraicGeometry.IsClosedImmersion f.left := hf
  exact Over.mono_of_mono_left f

/-- A representable open subsheaf of an algebraic space is an algebraic space. -/
theorem open_subsheaf_isAlgebraicSpace (Y : AlgebraicSpace S)
    (B : Subfunctor Y.presheaf) (hB : openMorphism B.ι)
    (hsh : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) B.toFunctor) :
    IsAlgebraicSpace S ⟨B.toFunctor, hsh⟩ := by
  refine ⟨?_, ?_⟩
  · apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro U b
    have sq : IsPullback (𝟙 _) b (b ≫ B.ι) B.ι :=
      IsPullback.of_horiz_isIso_mono ⟨by simp⟩
    exact MorphismProperty.of_isPullback
      (P := (schemeYoneda S).relativelyRepresentable) sq
      (Y.representable_from_scheme (b ≫ B.ι))
  · obtain ⟨U, a, _, ha, hs⟩ := Y.exists_atlas
    let hr := hB.rep
    refine ⟨hr.pullback a, hr.fst a, ?_, ?_⟩
    · exact MorphismProperty.of_isPullback
        (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
          (Over.forget S)).relative (schemeYoneda S)) (hr.isPullback a).flip ha
    · exact MorphismProperty.of_isPullback
        (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u})
          (Over.forget S)).relative (schemeYoneda S)) (hr.isPullback a).flip hs

/-- The sheaf represented by the image of a mono from a scheme. -/
lemma range_scheme_isSheaf {U : Over S} (a : (schemeYoneda S).obj U ⟶ F) [Mono a] :
    Presieve.IsSheaf (fppfTopology S) (Subfunctor.range a).toFunctor := by
  rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff
    (asIso (Subfunctor.toRange a))).mp ((schemeSheaf S).obj U).property

/-- Passing from a mono open chart to its image preserves its open property. -/
lemma range_open {U : Over S} (a : (schemeYoneda S).obj U ⟶ F)
    (ha : openMorphism a) :
    openMorphism (Subfunctor.range a).ι := by
  let := SliceOpenGluing.open_mono ha
  apply (openMorphism.cancel_left_of_respectsIso (Subfunctor.toRange a) _).mp
  simpa using ha

variable (X Y : AlgebraicSpace S) (i : X ⟶ Y) (hi : IsThickening (hom i))
    {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : openMorphism a)

def liftedSubfunctor : Subfunctor Y.presheaf :=
  universalImage (hom i) (Subfunctor.range a)

include ha in
lemma liftedSubfunctor_isSheaf :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S)
      (liftedSubfunctor X Y i a).toFunctor := by
  let := SliceOpenGluing.open_mono ha
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  exact universalImage_isSheaf (fppfTopology S) (hom i) (Subfunctor.range a)
    ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp X.toSheaf.property)
    ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp Y.toSheaf.property)
    (range_scheme_isSheaf a)

def liftedSpace : AlgebraicSpace S :=
  ⟨⟨(liftedSubfunctor X Y i a).toFunctor,
      liftedSubfunctor_isSheaf X Y i a ha⟩,
    open_subsheaf_isAlgebraicSpace Y (liftedSubfunctor X Y i a)
      (universalImage_open (hom i) hi _ (range_open a ha))
      (liftedSubfunctor_isSheaf X Y i a ha)⟩

def liftedInclusion : liftedSpace X Y i hi a ha ⟶ Y :=
  homMk (liftedSubfunctor X Y i a).ι

include hi in
lemma chart_lifts :
    Subfunctor.range (a ≫ hom i) ≤ liftedSubfunctor X Y i a := by
  let := thickening_mono (hom i) hi
  rw [Subfunctor.range_comp, Subfunctor.image_le_iff]
  change Subfunctor.range a ≤
    (universalImage (hom i) (Subfunctor.range a)).preimage (hom i)
  rw [universalImage_preimage_eq]

def liftedChart : (schemeToSpace S).obj U ⟶ liftedSpace X Y i hi a ha :=
  homMk (Subfunctor.lift (a ≫ hom i) (chart_lifts X Y i hi a))

lemma liftedChart_isPullback :
    IsPullback a (hom (liftedChart X Y i hi a ha)) (hom i)
      (hom (liftedInclusion X Y i hi a ha)) := by
  let := thickening_mono (hom i) hi
  let := SliceOpenGluing.open_mono ha
  apply IsPullback.flip
  apply isPullback_subfunctor_of_range (liftedSubfunctor X Y i a) _ a (hom i)
  · exact Subfunctor.lift_ι _ (chart_lifts X Y i hi a)
  · exact (universalImage_preimage_eq (hom i) (Subfunctor.range a)).symm

lemma liftedChart_thickening :
    IsThickening (hom (liftedChart X Y i hi a ha)) := by
  refine ⟨?_, ?_⟩
  · exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
        (Over.forget S)).relative (schemeYoneda S))
      (liftedChart_isPullback X Y i hi a ha) hi.closedImmersion
  · exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u})
        (Over.forget S)).relative (schemeYoneda S))
      (liftedChart_isPullback X Y i hi a ha) hi.surjective

end Relative

section Families

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {F : Presheaf S} {I : Type u} {U : I → Over S}

/-- Pulling back a locally covering family of representable maps gives a covering sieve. -/
lemma family_pullback_cover
    (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ F)
    (ha : ∀ k, IsRepresentableMorphism (a k))
    [CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a)]
    {R : Over S} (r : (schemeYoneda S).obj R ⟶ F) :
    Sieve.ofArrows (fun k ↦ (ha k).pullback r) (fun k ↦ (ha k).snd r) ∈
      (fppfTopology S) R := by
  apply (fppfTopology S).superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem (fppfTopology S) (Sigma.desc a)
      (uliftYonedaEquiv r))
  intro V v hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨⟨k⟩, ⟨z⟩, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op V))
      (coproductIsCoproduct (fun k ↦ (schemeYoneda S).obj (U k)))) w
  have hz : (a k).app (op V) (ULift.up z) =
      F.map v.op (uliftYonedaEquiv r) := by
    change (Sigma.desc a).app (op V)
      ((Sigma.ι (fun k ↦ (schemeYoneda S).obj (U k)) k).app (op V) (ULift.up z)) =
        F.map v.op (uliftYonedaEquiv r) at hw
    exact (congrArg (fun n : (schemeYoneda S).obj (U k) ⟶ F ↦
      n.app (op V) (ULift.up z)) (Sigma.ι_comp_desc a k)).symm.trans hw
  have hfac : (schemeYoneda S).map z ≫ a k = (schemeYoneda S).map v ≫ r := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    exact hz.trans (uliftYonedaEquiv_naturality r v.op)
  exact ⟨_, (ha k).lift ((schemeYoneda S).map z) v hfac, _, ⟨k⟩,
    (ha k).lift_snd _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
/-- An fppf covering sieve of scheme maps covers the underlying points. -/
lemma points_covered_of_fppf_cover {R : Over S} {W : I → Over S}
    (q : ∀ k, W k ⟶ R)
    (hq : Sieve.ofArrows W q ∈ (fppfTopology S) R) (x : R.left) :
    ∃ k z, (q k).left z = x := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hq
  have hq' := Scheme.grothendieckTopology_monotone
    (P := @_root_.AlgebraicGeometry.Flat.{u} ⊓
      @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    (Q := ⊤) le_top R.left hq
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology
    (P := ⊤) hq'
  obtain ⟨k, z, hz⟩ := 𝒰.exists_eq x
  obtain ⟨V, b, _, ⟨j⟩, hb⟩ := h𝒰 _ _ (Presieve.ofArrows.mk k)
  exact ⟨j, b z, (congrArg (fun f : 𝒰.X k ⟶ R.left ↦ f z) hb).trans hz⟩

/-- Transporting an open covering family across a thickening retains fppf coverage. -/
lemma lifted_maps_cover {R T : Over S} {W : I → Over S}
    (p : R ⟶ T) (q : ∀ k, W k ⟶ R)
    [_root_.AlgebraicGeometry.IsClosedImmersion p.left]
    [_root_.AlgebraicGeometry.Surjective p.left]
    [∀ k, _root_.AlgebraicGeometry.IsOpenImmersion (q k).left]
    (hq : Sieve.ofArrows W q ∈ (fppfTopology S) R) :
    Sieve.ofArrows (fun k ↦ liftedScheme p (q k))
      (fun k ↦ liftedMap p (q k)) ∈ (fppfTopology S) T := by
  have hpoints : ∀ x : T.left, ∃ k z, (liftedMap p (q k)).left z = x := by
    intro x
    obtain ⟨r, rfl⟩ := p.left.surjective x
    obtain ⟨k, z, hz⟩ := points_covered_of_fppf_cover q hq r
    have hx : p.left r ∈ Set.range (liftedMap p (q k)).left := by
      rw [range_liftedMap]
      exact ⟨r, ⟨z, hz⟩, rfl⟩
    obtain ⟨w, hw⟩ := hx
    exact ⟨k, w, hw⟩
  let 𝒰 := Scheme.Cover.mkOfCovers (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    I (fun k ↦ (liftedScheme p (q k)).left)
    (fun k ↦ (liftedMap p (q k)).left) hpoints
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono
    Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology

/-- The universal images of a covering open family still cover across a thickening. -/
theorem universalImage_family_locallySurjective {G : Presheaf S}
    (i : F ⟶ G) (hi : IsThickening i)
    (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ F)
    (ha : ∀ k, openMorphism (a k))
    [CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a)] :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (Sigma.desc (fun k ↦ (universalImage i (Subfunctor.range (a k))).ι)) := by
  constructor
  intro T y
  let g : (schemeYoneda S).obj T ⟶ G := uliftYonedaEquiv.symm y
  let hr := hi.closedImmersion.representable
  let R := hr.pullback g
  let r := hr.fst g
  let p : R ⟶ T := hr.snd g
  let W := fun k ↦ (ha k).rep.pullback r
  let q : ∀ k, W k ⟶ R := fun k ↦ (ha k).rep.snd r
  let : _root_.AlgebraicGeometry.IsClosedImmersion p.left :=
    hi.closedImmersion.projection g r p (hr.isPullback g)
  let : _root_.AlgebraicGeometry.Surjective p.left :=
    hi.surjective.projection g r p (hr.isPullback g)
  let : ∀ k, _root_.AlgebraicGeometry.IsOpenImmersion (q k).left := fun k ↦
    (ha k).property r ((ha k).rep.fst r) (q k) ((ha k).rep.isPullback r)
  have hq := family_pullback_cover a (fun k ↦ (ha k).rep) r
  have hcover := lifted_maps_cover p q hq
  apply (fppfTopology S).superset_covering ?_ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro k
  let B := universalImage i (Subfunctor.range (a k))
  let l := liftedMap p (q k)
  have hqrange : Subfunctor.range ((schemeYoneda S).map (q k)) =
      (Subfunctor.range (a k)).preimage r :=
    range_eq_preimage_of_isPullback ((ha k).rep.isPullback r)
  have hl : Subfunctor.range ((schemeYoneda S).map l) = B.preimage g := by
    rw [← universalImage_scheme_eq_range p (q k), hqrange,
      ← universalImage_preimage_of_isPullback (hr.isPullback g)]
  have hle : Subfunctor.range ((schemeYoneda S).map l ≫ g) ≤ B := by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, hl]
  let b := Subfunctor.lift ((schemeYoneda S).map l ≫ g) hle
  refine ⟨(Sigma.ι (fun k ↦ (universalImage i (Subfunctor.range (a k))).toFunctor)
    k).app _ (uliftYonedaEquiv b), ?_⟩
  have he := congrArg (fun n : B.toFunctor ⟶ G ↦
    n.app _ (uliftYonedaEquiv b))
    (Sigma.ι_comp_desc
      (fun k ↦ (universalImage i (Subfunctor.range (a k))).ι) k)
  change (Sigma.desc (fun k ↦ (universalImage i (Subfunctor.range (a k))).ι)).app _
      ((Sigma.ι (fun k ↦ (universalImage i (Subfunctor.range (a k))).toFunctor)
        k).app _ (uliftYonedaEquiv b)) = G.map l.op y
  refine he.trans ?_
  rw [← uliftYonedaEquiv_comp]
  change uliftYonedaEquiv
    (Subfunctor.lift ((schemeYoneda S).map l ≫ g) hle ≫ B.ι) = _
  rw [Subfunctor.lift_ι]
  exact (uliftYonedaEquiv_naturality g l.op).symm.trans
    (congrArg (G.map l.op) (Equiv.apply_symm_apply uliftYonedaEquiv.{u + 1} y))

end Families

/-- Actual lifted algebraic spaces, charts and covering family for every thickening. -/
theorem openFamilyLifting : OpenFamilyLiftingStatement.{u} := by
  intro S X Y i hi I U a ha hcover
  let := hcover
  refine ⟨(fun k ↦ liftedSpace X Y i hi (a k) (ha k)),
    (fun k ↦ liftedInclusion X Y i hi (a k) (ha k)),
    (fun k ↦ liftedChart X Y i hi (a k) (ha k)), ?_, ?_, ?_, ?_⟩
  · intro k
    exact universalImage_open (hom i) hi _ (range_open (a k) (ha k))
  · intro k
    exact liftedChart_thickening X Y i hi (a k) (ha k)
  · intro k
    exact liftedChart_isPullback X Y i hi (a k) (ha k)
  · exact universalImage_family_locallySurjective (hom i) hi a ha

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorLifting
