import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasComponentIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange

/-! # Point comparisons under restriction of the scheme base -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} (g : T ⟶ S)

/-- Forget the structure map to `T` on a represented test. -/
def forgetBaseYoneda (U : Over T) :
    (schemeYoneda T).obj U ⟶ (restrictPresheaf g).obj
      ((schemeYoneda S).obj ((Over.map g).obj U)) where
  app V := TypeCat.ofHom fun x => ULift.up ((Over.map g).map x.down)
  naturality {V W} f := by
    ext x
    exact congrArg ULift.up ((Over.map g).map_comp f.unop x.down)

@[reassoc]
theorem forgetBaseYoneda_naturality {U V : Over T} (f : U ⟶ V) :
    (schemeYoneda T).map f ≫ forgetBaseYoneda g V =
      forgetBaseYoneda g U ≫ (restrictPresheaf g).map
        ((schemeYoneda S).map ((Over.map g).map f)) := by
  ext W x
  exact congrArg ULift.up ((Over.map g).map_comp x.down f)

namespace FieldPoint

variable {g} {F : Presheaf S}

/-- A point of the restricted presheaf, viewed over the original base. -/
def forgetBase (p : FieldPoint ((restrictPresheaf g).obj F)) : FieldPoint F :=
  ⟨p.field, p.base ≫ g, p.val⟩

theorem forgetBase_rel {p q : FieldPoint ((restrictPresheaf g).obj F)}
    (h : Rel ((restrictPresheaf g).obj F) p q) :
    Rel F (p.forgetBase) (q.forgetBase) := by
  obtain ⟨Ω, _, i, j, hb, he⟩ := h
  refine ⟨Ω, inferInstance, i, j, ?_, ?_⟩
  · simpa only [forgetBase, Category.assoc] using congrArg (fun k => k ≫ g) hb
  · exact he

end FieldPoint

namespace Points

/-- The canonical point map from a restricted presheaf to the original presheaf. -/
def forgetBase (F : Presheaf S) : Points ((restrictPresheaf g).obj F) → Points F :=
  Quot.lift (fun p => Quot.mk _ p.forgetBase)
    (fun _ _ h => Quot.sound (FieldPoint.forgetBase_rel h))

@[simp]
theorem forgetBase_mk (F : Presheaf S)
    (p : FieldPoint ((restrictPresheaf g).obj F)) :
    forgetBase g F (Quot.mk _ p) = Quot.mk _ p.forgetBase := rfl

theorem forgetBase_map {F G : Presheaf S} (f : F ⟶ G)
    (x : Points ((restrictPresheaf g).obj F)) :
    forgetBase g G (map ((restrictPresheaf g).map f) x) =
      map f (forgetBase g F x) := by
  induction x using Quot.ind
  rfl

@[simp]
theorem forgetBase_schemePoint (U : Over T) (x : U.left) :
    forgetBase g ((schemeYoneda S).obj ((Over.map g).obj U))
      (map (forgetBaseYoneda g U) (schemePoint U x)) =
        schemePoint ((Over.map g).obj U) x := by
  apply (schemePointsEquiv ((Over.map g).obj U)).injective
  rfl

end Points

/-- Forgetting the base on the point map of a chart gives its original chart map. -/
theorem forgetBase_chartPointMap {F : Presheaf S} (U : Over T)
    (a : (schemeYoneda S).obj ((Over.map g).obj U) ⟶ F) (x : U.left) :
    Points.forgetBase g F
      (chartPointMap (forgetBaseYoneda g U ≫ (restrictPresheaf g).map a) x) =
        chartPointMap a x := by
  dsimp only [chartPointMap, Function.comp_apply]
  rw [Points.map_comp, Points.forgetBase_map, Points.forgetBase_schemePoint]

/-- Evaluation at the identity test recovers a chart from its restriction over `T`. -/
theorem forgetBaseYoneda_comp_injective (U : Over T) {F : Presheaf S}
    {a b : (schemeYoneda S).obj ((Over.map g).obj U) ⟶ F}
    (h : forgetBaseYoneda g U ≫ (restrictPresheaf g).map a =
      forgetBaseYoneda g U ≫ (restrictPresheaf g).map b) : a = b := by
  apply uliftYonedaEquiv.{u + 1}.injective
  have he := congrArg (fun k => k.app (op U) (ULift.up (𝟙 U))) h
  change a.app _ (ULift.up ((Over.map g).map (𝟙 U))) =
    b.app _ (ULift.up ((Over.map g).map (𝟙 U))) at he
  rw [(Over.map g).map_id U] at he
  exact he

/-- A common chart over two bases has the same point relation if the original
chart recovers its map to `T` and the comparison is a monomorphism. -/
theorem sameImage₂_forgetBase_iff {F : Presheaf S} {C : Presheaf T} (U : Over T)
    (a : (schemeYoneda T).obj U ⟶ C)
    (b : (schemeYoneda S).obj ((Over.map g).obj U) ⟶ F)
    (v : C ⟶ (restrictPresheaf g).obj F) [Mono v]
    (rho : F ⟶ (schemeYoneda S).obj (Over.mk g))
    (hb : b ≫ rho = (schemeYoneda S).map (Over.homMk U.hom rfl))
    (w : a ≫ v = forgetBaseYoneda g U ≫ (restrictPresheaf g).map b)
    (x y : U.left) : SameImage₂ a a x y ↔ SameImage₂ b b x y := by
  have hw {W : Over T} (k : W ⟶ U) :
      ((schemeYoneda T).map k ≫ a) ≫ v =
        forgetBaseYoneda g W ≫ (restrictPresheaf g).map
          ((schemeYoneda S).map ((Over.map g).map k) ≫ b) := by
    rw [Category.assoc, w, ← Category.assoc, forgetBaseYoneda_naturality,
      Category.assoc, ← Functor.map_comp]
  constructor
  · rintro ⟨W, l, r, t, he, hl, hr⟩
    refine ⟨(Over.map g).obj W, (Over.map g).map l, (Over.map g).map r, t, ?_, hl, hr⟩
    apply forgetBaseYoneda_comp_injective g W
    rw [← hw l, ← hw r, he]
  · rintro ⟨W, l, r, t, he, hl, hr⟩
    have hs := congrArg (fun k => k ≫ rho) he
    simp only [Category.assoc, hb, ← Functor.map_comp] at hs
    have hs' := (schemeYoneda S).map_injective hs
    have ht : l.left ≫ U.hom = r.left ≫ U.hom := congrArg CommaMorphism.left hs'
    let WT : Over T := Over.mk (l.left ≫ U.hom)
    let lT : WT ⟶ U := Over.homMk l.left rfl
    let rT : WT ⟶ U := Over.homMk r.left ht.symm
    let k : (Over.map g).obj WT ⟶ W := Over.homMk (𝟙 _) (by
      simp only [Over.map_obj_hom, WT, Over.mk_hom, Category.id_comp, Category.assoc]
      exact (Over.w l).symm)
    have hkL : (Over.map g).map lT = k ≫ l := by ext; simp [k, lT]
    have hkR : (Over.map g).map rT = k ≫ r := by ext; simp [k, rT]
    refine ⟨WT, lT, rT, t, ?_, hl, hr⟩
    apply (cancel_mono v).mp
    have eh : (schemeYoneda S).map (k ≫ l) ≫ b =
        (schemeYoneda S).map (k ≫ r) ≫ b := by
      simp only [Functor.map_comp, Category.assoc, he]
    rw [hw lT, hw rT, hkL, hkR, eh]

/-- The forgetful point map is a homeomorphism when two bases share a
surjective étale chart with its recoverable structure map. -/
def forgetBasePointsHomeomorph {F : Presheaf S} {C : Presheaf T} (U : Over T)
    (a : (schemeYoneda T).obj U ⟶ C)
    (b : (schemeYoneda S).obj ((Over.map g).obj U) ⟶ F)
    (v : C ⟶ (restrictPresheaf g).obj F) [Mono v]
    (rho : F ⟶ (schemeYoneda S).obj (Over.mk g))
    (hb : b ≫ rho = (schemeYoneda S).map (Over.homMk U.hom rfl))
    (w : a ≫ v = forgetBaseYoneda g U ≫ (restrictPresheaf g).map b)
    (ha : IsEtale a) (hsa : IsSurjective a) (hbEt : IsEtale b) (hsb : IsSurjective b) :
    @Homeomorph (Points C) (Points F) (pointTopology C) (pointTopology F) := by
  letI := pointTopology C
  letI := pointTopology F
  let q : Points C → Points F := Points.forgetBase g F ∘ Points.map v
  have hq (x : U.left) : q (chartPointMap a x) = chartPointMap b x := by
    dsimp only [q, Function.comp_apply, chartPointMap]
    rw [← Points.map_comp, w]
    exact forgetBase_chartPointMap g U b x
  have hi : Function.Injective q := by
    intro p₁ p₂ he
    obtain ⟨x, rfl⟩ := surjective_chartPointMap a hsa p₁
    obtain ⟨y, rfl⟩ := surjective_chartPointMap a hsa p₂
    rw [hq, hq] at he
    apply (chartPointMap_eq_iff_sameImage₂ a a x y).mpr
    exact (sameImage₂_forgetBase_iff g U a b v rho hb w x y).mpr
      ((chartPointMap_eq_iff_sameImage₂ b b x y).mp he)
  have hs : Function.Surjective q := by
    intro p
    obtain ⟨x, rfl⟩ := surjective_chartPointMap b hsb p
    exact ⟨chartPointMap a x, hq x⟩
  let e : Points C ≃ Points F := Equiv.ofBijective q ⟨hi, hs⟩
  have qa := isQuotientMap_chartPointMap a ha hsa
  have qb := isQuotientMap_chartPointMap b hbEt hsb
  refine ⟨e, ?_, ?_⟩
  · apply qa.continuous_iff.mpr
    change Continuous (q ∘ chartPointMap a)
    have h : q ∘ chartPointMap a = chartPointMap b := funext hq
    rw [h]
    exact qb.continuous
  · apply qb.continuous_iff.mpr
    change Continuous (e.symm ∘ chartPointMap b)
    have h : e.symm ∘ chartPointMap b = chartPointMap a := by
      funext x
      apply e.injective
      exact (e.apply_symm_apply (chartPointMap b x)).trans (hq x).symm
    rw [h]
    exact qa.continuous


end Langlands.AlgebraicGeometry.AlgebraicSpace
