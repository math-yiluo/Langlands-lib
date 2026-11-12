import Langlands.AlgebraicGeometry.AlgebraicSpace.CommonAtlasPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct

/-! # The same geometric fibre over two scheme bases -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S T : Scheme.{u}} (g : T ⟶ S)

instance mono_forgetBaseYoneda (U : Over T) : Mono (forgetBaseYoneda g U) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [mono_iff_injective]
  intro x y he
  apply ULift.ext
  have h : (Over.map g).map x.down = (Over.map g).map y.down := congrArg ULift.down he
  have hh := congrArg (fun k : (Over.map g).obj W.unop ⟶ (Over.map g).obj U => k.left) h
  exact Over.OverMorphism.ext hh

/-- Forgetting the base is cartesian for every morphism of represented tests. -/
theorem isPullback_forgetBaseYoneda {U V : Over T} (f : U ⟶ V) :
    IsPullback ((schemeYoneda T).map f) (forgetBaseYoneda g U)
      (forgetBaseYoneda g V)
      ((restrictPresheaf g).map ((schemeYoneda S).map ((Over.map g).map f))) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  obtain ⟨W⟩ := W
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (forgetBaseYoneda_naturality g f) (op W), ?_, ?_⟩
  · rintro ⟨x⟩ ⟨y⟩ ⟨_, he⟩
    apply ULift.ext
    have h : (Over.map g).map x = (Over.map g).map y := congrArg ULift.down he
    have hh := congrArg (fun k : (Over.map g).obj W ⟶ (Over.map g).obj U => k.left) h
    exact Over.OverMorphism.ext hh
  · rintro ⟨a⟩ ⟨b⟩ he
    have he' : (Over.map g).map a = b ≫ (Over.map g).map f := congrArg ULift.down he
    have hl : a.left = b.left ≫ f.left := congrArg CommaMorphism.left he'
    let c : W ⟶ U := Over.homMk b.left (by
      rw [← Over.w f, ← Category.assoc, ← hl]
      exact Over.w a)
    refine ⟨ULift.up c, ?_, ?_⟩
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hl.symm
    · apply ULift.ext
      apply Over.OverMorphism.ext
      rfl

/-- The same section on a represented test, regarded as a chart over `S`. -/
def originalBaseChart {F : Presheaf S} {V : Over T}
    (a : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj F) :
    (schemeYoneda S).obj ((Over.map g).obj V) ⟶ F :=
  uliftYonedaEquiv.{u + 1}.symm (a.app (op V) (ULift.up (𝟙 V)))

@[reassoc (attr := simp)]
theorem originalBaseChart_restrict {F : Presheaf S} {V : Over T}
    (a : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj F) :
    forgetBaseYoneda g V ≫ (restrictPresheaf g).map (originalBaseChart g a) = a := by
  apply uliftYonedaEquiv.{u + 1}.injective
  change (originalBaseChart g a).app _ (ULift.up ((Over.map g).map (𝟙 V))) = _
  rw [(Over.map g).map_id V]
  change uliftYonedaEquiv.{u + 1} (originalBaseChart g a) = uliftYonedaEquiv.{u + 1} a
  simp only [originalBaseChart, Equiv.apply_symm_apply]
  rfl

section Fibre

variable {X Y : Presheaf S} (f : X ⟶ Y) {V : Over T}
    (y : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj Y)

/-- The actual comparison between a fibre over `T` and the restricted fibre over `S`. -/
def fibreRestrictionMap :
    Limits.pullback ((restrictPresheaf g).map f) y ⟶
      (restrictPresheaf g).obj (Limits.pullback f (originalBaseChart g y)) :=
  ((IsPullback.of_hasPullback f (originalBaseChart g y)).map (restrictPresheaf g)).lift
    (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ forgetBaseYoneda g V) (by
      rw [Category.assoc, originalBaseChart_restrict]
      exact Limits.pullback.condition)

@[reassoc (attr := simp)]
theorem fibreRestrictionMap_fst :
    fibreRestrictionMap g f y ≫ (restrictPresheaf g).map
      (Limits.pullback.fst f (originalBaseChart g y)) =
        Limits.pullback.fst ((restrictPresheaf g).map f) y :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem fibreRestrictionMap_snd :
    fibreRestrictionMap g f y ≫ (restrictPresheaf g).map
      (Limits.pullback.snd f (originalBaseChart g y)) =
        Limits.pullback.snd ((restrictPresheaf g).map f) y ≫ forgetBaseYoneda g V :=
  IsPullback.lift_snd _ _ _ _

/-- The fibre comparison is the Limits.pullback of the forgetful map on the represented target. -/
theorem fibreRestrictionMap_isPullback :
    IsPullback (fibreRestrictionMap g f y) (Limits.pullback.snd ((restrictPresheaf g).map f) y)
      ((restrictPresheaf g).map (Limits.pullback.snd f (originalBaseChart g y)))
      (forgetBaseYoneda g V) := by
  have h := (IsPullback.of_hasPullback f (originalBaseChart g y)).map (restrictPresheaf g)
  apply IsPullback.of_right (t := h)
  · rw [fibreRestrictionMap_fst, originalBaseChart_restrict]
    exact (IsPullback.of_hasPullback ((restrictPresheaf g).map f) y)
  · exact fibreRestrictionMap_snd g f y

instance mono_fibreRestrictionMap : Mono (fibreRestrictionMap g f y) :=
  (fibreRestrictionMap_isPullback g f y).mono_fst_of_mono

/-- A single actual scheme atlas for the same fibre viewed over either base. -/
structure FibreRestrictionAtlas where
  source : Over T
  map : (schemeYoneda T).obj source ⟶ Limits.pullback ((restrictPresheaf g).map f) y
  originalMap : (schemeYoneda S).obj ((Over.map g).obj source) ⟶
    Limits.pullback f (originalBaseChart g y)
  projection : source ⟶ V
  original_snd : originalMap ≫ Limits.pullback.snd f (originalBaseChart g y) =
    (schemeYoneda S).map ((Over.map g).map projection)
  square : map ≫ fibreRestrictionMap g f y =
    forgetBaseYoneda g source ≫ (restrictPresheaf g).map originalMap
  etale : IsEtale map
  surjective : IsSurjective map
  originalEtale : IsEtale originalMap
  originalSurjective : IsSurjective originalMap

/-- An atlas of the original fibre acquires its unique structure over `T`,
and remains an atlas of the fibre over `T`. -/
def FibreRestrictionAtlas.of_original {W : Over S}
    (b₀ : (schemeYoneda S).obj W ⟶ Limits.pullback f (originalBaseChart g y))
    (hbe : IsEtale b₀) (hbs : IsSurjective b₀) : FibreRestrictionAtlas g f y := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange.respectsIso
  let pS : W ⟶ (Over.map g).obj V :=
    (schemeYoneda S).preimage (b₀ ≫ Limits.pullback.snd f (originalBaseChart g y))
  have hpS : (schemeYoneda S).map pS = b₀ ≫ Limits.pullback.snd f (originalBaseChart g y) :=
    Functor.map_preimage _ _
  let U : Over T := Over.mk (pS.left ≫ V.hom)
  let k : (Over.map g).obj U ≅ W := Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom, U, Over.mk_hom,
      Category.assoc]
    exact (Over.w pS).symm)
  let p : U ⟶ V := Over.homMk pS.left rfl
  have hk : k.hom ≫ pS = (Over.map g).map p := by ext; simp [k, p]
  let b := (schemeYoneda S).map k.hom ≫ b₀
  have hb : b ≫ Limits.pullback.snd f (originalBaseChart g y) =
      (schemeYoneda S).map ((Over.map g).map p) := by
    dsimp only [b]
    rw [Category.assoc, ← hpS, ← Functor.map_comp, hk]
  have hw : (b ≫ Limits.pullback.fst f (originalBaseChart g y)) ≫ f =
      (schemeYoneda S).map ((Over.map g).map p) ≫ originalBaseChart g y := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hb]
  have hcomm : (forgetBaseYoneda g U ≫ (restrictPresheaf g).map
      (b ≫ Limits.pullback.fst f (originalBaseChart g y))) ≫ (restrictPresheaf g).map f =
        (schemeYoneda T).map p ≫ y := by
    rw [Category.assoc, ← Functor.map_comp, hw, Functor.map_comp,
      ← Category.assoc, ← forgetBaseYoneda_naturality, Category.assoc,
      originalBaseChart_restrict]
  let a := Limits.pullback.lift
    (forgetBaseYoneda g U ≫ (restrictPresheaf g).map
      (b ≫ Limits.pullback.fst f (originalBaseChart g y))) ((schemeYoneda T).map p) hcomm
  have ha : a ≫ fibreRestrictionMap g f y =
      forgetBaseYoneda g U ≫ (restrictPresheaf g).map b := by
    apply ((IsPullback.of_hasPullback f (originalBaseChart g y)).map
      (restrictPresheaf g)).hom_ext
    · dsimp only [a]
      rw [Category.assoc, fibreRestrictionMap_fst, Limits.pullback.lift_fst]
      simp only [Functor.map_comp, Category.assoc, b]
    · dsimp only [a]
      rw [Category.assoc, fibreRestrictionMap_snd, ← Category.assoc,
        Limits.pullback.lift_snd, forgetBaseYoneda_naturality,
        Category.assoc, ← Functor.map_comp, hb]
  have hcart : IsPullback a (forgetBaseYoneda g U) (fibreRestrictionMap g f y)
      ((restrictPresheaf g).map b) := by
    apply IsPullback.of_right (t := (fibreRestrictionMap_isPullback g f y).flip)
    · dsimp only [a]
      rw [Limits.pullback.lift_snd, ← Functor.map_comp, hb]
      exact isPullback_forgetBaseYoneda g p
    · exact ha
  have hbe' : IsEtale b := IsEtale.iso_comp ((schemeYoneda S).mapIso k) hbe
  have hbs' : IsSurjective b := MorphismProperty.RespectsIso.precomp
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _ hbs
  refine ⟨U, a, b, p, hb, ha, ?_, ?_, hbe', hbs'⟩
  · exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget T)).relative
        (schemeYoneda T)) hcart.flip (relative_restrictPresheaf_map (@Etale.{u}) hbe')
  · exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget T)).relative
        (schemeYoneda T)) hcart.flip (relative_restrictPresheaf_map (@Surjective.{u}) hbs')

/-- The common atlas identifies the two point topologies by the actual fibre comparison. -/
def FibreRestrictionAtlas.pointsHomeomorph (a : FibreRestrictionAtlas g f y) :
    @Homeomorph (Points (Limits.pullback ((restrictPresheaf g).map f) y))
      (Points (Limits.pullback f (originalBaseChart g y))) (pointTopology _) (pointTopology _) := by
  apply forgetBasePointsHomeomorph g a.source a.map a.originalMap (fibreRestrictionMap g f y)
    (Limits.pullback.snd f (originalBaseChart g y) ≫
      (schemeYoneda S).map (Over.homMk V.hom rfl))
  · rw [← Category.assoc, a.original_snd, ← Functor.map_comp]
    congr 1
    ext
    exact Over.w a.projection
  · exact a.square
  · exact a.etale
  · exact a.surjective
  · exact a.originalEtale
  · exact a.originalSurjective


end Fibre

/-- The original fibre of a morphism of algebraic spaces supplies the required atlas. -/
theorem nonempty_fibreRestrictionAtlas {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over T}
    (y : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj Y.presheaf) :
    Nonempty (FibreRestrictionAtlas g (hom f) y) := by
  let y₀ : (schemeToSpace S).obj ((Over.map g).obj V) ⟶ Y :=
    homMk (originalBaseChart g y)
  let F := fibreProduct f y₀
  obtain ⟨W, b, hbe, hbs⟩ := F.property.2
  let e := FibreProduct.presheafIso f y₀
  exact ⟨FibreRestrictionAtlas.of_original g (hom f) y (b ≫ e.hom)
    (hbe.comp_iso e) (hbs.comp_iso e)⟩

/-- A fibre of a base-changed space morphism has exactly the topology of the
same fibre viewed over the original base. -/
def fibreRestrictionPointsHomeomorph {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over T}
    (y : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj Y.presheaf) :
    @Homeomorph (Points (Limits.pullback (hom (baseChangeMap g f)) y))
      (Points (Limits.pullback (hom f) (originalBaseChart g y)))
      (pointTopology _) (pointTopology _) :=
  (Classical.choice (nonempty_fibreRestrictionAtlas g f y)).pointsHomeomorph g (hom f) y

@[simp]
theorem fibreRestrictionPointsHomeomorph_apply {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over T}
    (y : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj Y.presheaf)
    (x : Points (Limits.pullback (hom (baseChangeMap g f)) y)) :
    fibreRestrictionPointsHomeomorph g f y x =
      Points.forgetBase g (Limits.pullback (hom f) (originalBaseChart g y))
        (Points.map (fibreRestrictionMap g (hom f) y) x) := rfl

/-- The points of a represented scheme are independent of which scheme base is recorded. -/
def forgetBaseSchemePointsHomeomorph (V : Over T) :
    @Homeomorph (Points ((schemeYoneda T).obj V))
      (Points ((schemeYoneda S).obj ((Over.map g).obj V)))
      (pointTopology _) (pointTopology _) := by
  letI := pointTopology ((schemeYoneda T).obj V)
  letI := pointTopology ((schemeYoneda S).obj ((Over.map g).obj V))
  exact (schemePointsHomeomorph V).trans (schemePointsHomeomorph ((Over.map g).obj V)).symm

theorem forgetBaseSchemePointsHomeomorph_apply (V : Over T)
    (x : Points ((schemeYoneda T).obj V)) :
    forgetBaseSchemePointsHomeomorph g V x =
      Points.forgetBase g ((schemeYoneda S).obj ((Over.map g).obj V))
        (Points.map (forgetBaseYoneda g V) x) := by
  apply (schemePointsEquiv ((Over.map g).obj V)).injective
  change schemePointsTo ((Over.map g).obj V)
    (schemePoint ((Over.map g).obj V) (schemePointsTo V x)) = _
  rw [schemePointsTo_schemePoint]
  induction x using Quot.ind
  rfl

/-- The homeomorphism of fibre point spaces commutes with projection to the
same underlying represented target scheme. -/
theorem fibreRestrictionPointsHomeomorph_snd {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over T}
    (y : (schemeYoneda T).obj V ⟶ (restrictPresheaf g).obj Y.presheaf)
    (x : Points (Limits.pullback (hom (baseChangeMap g f)) y)) :
    Points.map (Limits.pullback.snd (hom f) (originalBaseChart g y))
      (fibreRestrictionPointsHomeomorph g f y x) =
        forgetBaseSchemePointsHomeomorph g V
          (Points.map (Limits.pullback.snd (hom (baseChangeMap g f)) y) x) := by
  rw [fibreRestrictionPointsHomeomorph_apply, ← Points.forgetBase_map,
    ← Points.map_comp, fibreRestrictionMap_snd, Points.map_comp,
    forgetBaseSchemePointsHomeomorph_apply]
  rfl


end Langlands.AlgebraicGeometry.AlgebraicSpace
