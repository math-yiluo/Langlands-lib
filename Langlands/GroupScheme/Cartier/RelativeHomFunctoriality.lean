import Langlands.GroupScheme.Cartier.RelativeHomPostcompose

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier
universe u
variable {S : Scheme.{u}}

/-! ### Restriction on points -/

/-- Restriction commutes with the canonical projections `G_{T'} ⟶ G_T` and `H_{T'} ⟶ H_T`. -/
@[reassoc]
lemma restrict_baseChangeProj (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) :
    CommGroupScheme.hom (restrict G H a χ) ≫ baseChangeProj H a =
      baseChangeProj G a ≫ CommGroupScheme.hom χ := by
  have hr : CommGroupScheme.hom (restrict G H a χ) ≫ pullback.snd H.X.hom T'.hom =
      pullback.snd G.X.hom T'.hom :=
    Over.w (CommGroupScheme.groupHom (restrict G H a χ)).hom.hom
  have hχ : CommGroupScheme.hom χ ≫ pullback.snd H.X.hom T.hom =
      pullback.snd G.X.hom T.hom :=
    Over.w (CommGroupScheme.groupHom χ).hom.hom
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeProj_fst, restrict_fst, Category.assoc]
  · rw [Category.assoc, baseChangeProj_snd, ← Category.assoc, hr, Category.assoc, hχ,
      baseChangeProj_snd]

/-- A scheme `U` over `T'` is the same object over `S` whether it is regarded through `T'` or
through `a : T' ⟶ T` and `T`. -/
def restrictOverIso {T T' : Over S} (a : T' ⟶ T) (U : Over T'.left) :
    (Over.map T.hom).obj ((Over.map a.left).obj U) ≅ (Over.map T'.hom).obj U :=
  Over.isoMk (Iso.refl _) (by simp [Over.w a])

/-- The canonical identification of `U`-points of `G_{T'}` with `U`-points of `G_T`, where
`U` over `T'` is regarded over `T` through `a`. Both sides are identified with `U`-points of `G`
by `baseChangePointsEquiv`. -/
def restrictPointsEquiv (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (U : Over T'.left) :
    (U ⟶ (testBaseChange T' G).X) ≃* ((Over.map a.left).obj U ⟶ (testBaseChange T G).X) :=
  (baseChangePointsEquiv T'.hom G.toGrp U).trans
    ((((yonedaGrpObj G.X).mapIso (restrictOverIso a U).op).groupIsoToMulEquiv).trans
      (baseChangePointsEquiv T.hom G.toGrp ((Over.map a.left).obj U)).symm)

/-- The defining property of `restrictPointsEquiv`: both points give the same point of `G`. -/
lemma baseChangePointsEquiv_restrictPointsEquiv (G : CommGroupScheme S) {T T' : Over S}
    (a : T' ⟶ T) (U : Over T'.left) (x : U ⟶ (testBaseChange T' G).X) :
    baseChangePointsEquiv T.hom G.toGrp ((Over.map a.left).obj U)
        (restrictPointsEquiv G a U x) =
      (restrictOverIso a U).hom ≫ baseChangePointsEquiv T'.hom G.toGrp U x :=
  MulEquiv.apply_symm_apply _ _

/-- Concretely, `restrictPointsEquiv` composes a point with the canonical projection. -/
@[simp]
lemma restrictPointsEquiv_left (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (U : Over T'.left) (x : U ⟶ (testBaseChange T' G).X) :
    (restrictPointsEquiv G a U x).left = x.left ≫ baseChangeProj G a := by
  have h := congrArg CommaMorphism.left (baseChangePointsEquiv_restrictPointsEquiv G a U x)
  have hy : (restrictPointsEquiv G a U x).left ≫ pullback.snd G.X.hom T.hom =
      U.hom ≫ a.left :=
    Over.w (restrictPointsEquiv G a U x)
  have hx : x.left ≫ pullback.snd G.X.hom T'.hom = U.hom := Over.w x
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeProj_fst]
    have h' : (restrictPointsEquiv G a U x).left ≫ pullback.fst G.X.hom T.hom =
        𝟙 U.left ≫ x.left ≫ pullback.fst G.X.hom T'.hom := h
    rw [h', Category.id_comp]
  · rw [hy, Category.assoc, baseChangeProj_snd, ← Category.assoc, hx]

/-- The point formula for restriction: under the canonical identification of `U`-points, the
restriction of `χ` along `a` acts on points of `G_{T'}` as `χ` acts on the same points of
`G_T`. -/
lemma restrictPointsEquiv_restrict (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) (U : Over T'.left) (x : U ⟶ (testBaseChange T' G).X) :
    restrictPointsEquiv H a U (x ≫ (restrict G H a χ).toMul.hom.hom) =
      restrictPointsEquiv G a U x ≫ χ.toMul.hom.hom := by
  apply Over.OverMorphism.ext
  rw [restrictPointsEquiv_left, Over.comp_left, Over.comp_left, restrictPointsEquiv_left]
  change (x.left ≫ CommGroupScheme.hom (restrict G H a χ)) ≫ baseChangeProj H a =
    (x.left ≫ baseChangeProj G a) ≫ CommGroupScheme.hom χ
  rw [Category.assoc, restrict_baseChangeProj, Category.assoc]

/-- The point formula in terms of `baseChangePointsEquiv`: the `U`-point of `H` obtained from
the restricted morphism is the `U`-point obtained from `χ` on the same point of `G`, regarded
over `T`. -/
lemma baseChangePointsEquiv_restrict (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) (U : Over T'.left) (x : U ⟶ (testBaseChange T' G).X) :
    baseChangePointsEquiv T'.hom H.toGrp U (x ≫ (restrict G H a χ).toMul.hom.hom) =
      (restrictOverIso a U).inv ≫ baseChangePointsEquiv T.hom H.toGrp ((Over.map a.left).obj U)
        (restrictPointsEquiv G a U x ≫ χ.toMul.hom.hom) := by
  rw [← restrictPointsEquiv_restrict, baseChangePointsEquiv_restrictPointsEquiv,
    Iso.inv_hom_id_assoc]

/-- Restriction of a base-changed global homomorphism is its base change to the smaller test
scheme. -/
lemma restrict_baseChange_map {G H : CommGroupScheme S} (f : G ⟶ H) {T T' : Over S}
    (a : T' ⟶ T) :
    restrict G H a ((CommGroupScheme.baseChange T.hom).map f) =
      (CommGroupScheme.baseChange T'.hom).map f := by
  apply relativeHom_ext
  rw [restrict_fst, baseChange_map_fst, baseChange_map_fst, baseChangeProj_fst_assoc]

/-! ### The three-variable relative Hom functor -/

/-- The relative Hom functor `(G, H, T) ↦ Hom_T(G_T, H_T)`, contravariant in the source group
scheme, covariant in the target group scheme and contravariant in the test scheme. -/
def relativeHomTrifunctor :
    (CommGroupScheme S)ᵒᵖ ⥤ CommGroupScheme S ⥤ (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj G := relativeHomTargetFunctor G.unop
  map φ :=
    { app H := precomposeNatTrans H φ.unop
      naturality _ _ ψ := precomposeNatTrans_postcomposeNatTrans φ.unop ψ }
  map_id G := by
    ext H : 2
    exact precomposeNatTrans_id H G.unop
  map_comp φ φ' := by
    ext H : 2
    exact precomposeNatTrans_comp H φ'.unop φ.unop

@[simp]
lemma relativeHomTrifunctor_obj_obj (G H : CommGroupScheme S) :
    (relativeHomTrifunctor.obj (op G)).obj H = relativeHomFunctor G H := rfl

@[simp]
lemma relativeHomTrifunctor_obj_map (G : CommGroupScheme S) {H H' : CommGroupScheme S}
    (ψ : H ⟶ H') : (relativeHomTrifunctor.obj (op G)).map ψ = postcomposeNatTrans G ψ := rfl

@[simp]
lemma relativeHomTrifunctor_map_app {G' G : CommGroupScheme S} (φ : G' ⟶ G)
    (H : CommGroupScheme S) :
    (relativeHomTrifunctor.map φ.op).app H = precomposeNatTrans H φ := rfl

/-- Fixing the target recovers the relative Hom functor contravariant in the source. -/
lemma relativeHomTrifunctor_flip_obj (H : CommGroupScheme S) :
    (relativeHomTrifunctor (S := S)).flip.obj H = relativeHomBifunctor H := rfl

end Langlands.GroupScheme.Cartier
