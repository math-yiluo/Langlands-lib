import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
universe u
variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  (G : GroupScheme B)

/-- A group pulled back from B has its canonical descent identification along a map over B. -/
def descentBaseChangeIso :
    (Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G) ≅
      (Over.pullback b).mapGrp.obj G :=
  (baseChangeCompIso b a G).symm ≪≫
    eqToIso (congrArg (fun c => (Over.pullback c).mapGrp.obj G) ha)

/-- On the underlying B-scheme, changing the S-structure by a leaves a test scheme unchanged. -/
def descentTestIso (T : Over S) :
    (Over.map b).obj T ≅ (Over.map b).obj ((Over.map a).obj T) :=
  Over.isoMk (Iso.refl _) (by simp [ha])

set_option backward.isDefEq.respectTransparency false in
/-- The descent identification preserves the projection to the original group over B. -/
@[reassoc] theorem descentBaseChangeIso_hom_fst :
    (descentBaseChangeIso b a ha G).hom.hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst (pullback.snd G.X.hom b) a ≫ pullback.fst G.X.hom b := by
  have heq : ∀ {c d : S ⟶ B} (h : c = d),
      (eqToIso (congrArg (fun k => (Over.pullback k).mapGrp.obj G) h)).hom.hom.hom.left ≫
        pullback.fst G.X.hom d = pullback.fst G.X.hom c := by
    intro c d h
    subst d
    exact Category.id_comp _
  change ((baseChangeCompIso b a G).inv.hom.hom.left ≫ _) ≫ _ = _
  rw [Category.assoc, heq ha, baseChangeCompIso_inv_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The descent isomorphism is the identity on the resulting points of G over B. -/
theorem baseChangePointsEquiv_descent (T : Over S)
    (y : T ⟶ ((Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G)).X) :
    baseChangePointsEquiv b G T (y ≫ (descentBaseChangeIso b a ha G).hom.hom.hom) =
      (descentTestIso b a ha T).hom ≫
        baseChangePointsEquiv b G ((Over.map a).obj T)
          (baseChangePointsEquiv a ((Over.pullback b).mapGrp.obj G) T y) := by
  apply Over.OverMorphism.ext
  change (y.left ≫ (descentBaseChangeIso b a ha G).hom.hom.hom.left) ≫
      pullback.fst G.X.hom b =
    𝟙 T.left ≫ ((y.left ≫ pullback.fst (pullback.snd G.X.hom b) a) ≫
      pullback.fst G.X.hom b)
  rw [Category.id_comp, Category.assoc, descentBaseChangeIso_hom_fst, Category.assoc]

/-- Descend a cocharacter pulled back along a base endomorphism over B. -/
def transportCocharacter
    (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G) :
    (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G :=
  (Gm.baseChangeIso a).inv ≫ (Over.pullback a).mapGrp.map χ ≫
    (descentBaseChangeIso b a ha G).hom

/-- Transport evaluates the original cocharacter on the same unit with the changed S-structure. -/
theorem transportCocharacter_points
    (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G)
    (T : Over S) (x : T ⟶ (Gm S).X) :
    baseChangePointsEquiv b G T (x ≫ (transportCocharacter b a ha G χ).hom.hom) =
      (descentTestIso b a ha T).hom ≫
        baseChangePointsEquiv b G ((Over.map a).obj T)
          ((Gm.pointsEquiv S ((Over.map a).obj T)).symm (Gm.pointsEquiv S T x) ≫
            χ.hom.hom) := by
  change baseChangePointsEquiv b G T
    (((x ≫ (Gm.baseChangeIso a).inv.hom.hom) ≫
      ((Over.pullback a).mapGrp.map χ).hom.hom) ≫
        (descentBaseChangeIso b a ha G).hom.hom.hom) = _
  rw [baseChangePointsEquiv_descent, baseChangePointsEquiv_comp]
  congr 3
  apply (Gm.pointsEquiv S ((Over.map a).obj T)).injective
  rw [MulEquiv.apply_symm_apply]
  exact Gm.baseChangeUnitsEquiv_baseChangeIso_inv a T x

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along the identity leaves a cocharacter unchanged. -/
theorem transportCocharacter_id
    (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G) :
    transportCocharacter b (𝟙 S) (Category.id_comp b) G χ = χ := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv b G T).injective
  rw [transportCocharacter_points]
  let e : T ≅ (Over.map (𝟙 S)).obj T := Over.isoMk (Iso.refl _) (by simp)
  have hx : e.hom ≫ (Gm.pointsEquiv S ((Over.map (𝟙 S)).obj T)).symm
      (Gm.pointsEquiv S T x) = x := by
    apply (Gm.pointsEquiv S T).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    change Units.map (𝟙 T.left : T.left ⟶ T.left).appTop.hom.toMonoidHom _ = _
    simp
  have he : (descentTestIso b (𝟙 S) (Category.id_comp b) T).hom =
      (Over.map b).map e.hom := by
    apply Over.OverMorphism.ext
    rfl
  rw [he, ← baseChangePointsEquiv_naturality, ← Category.assoc, hx]

set_option backward.isDefEq.respectTransparency false in
/-- Successive transports compose in the geometric order of the base maps. -/
theorem transportCocharacter_comp (c : S ⟶ S) (hc : c ≫ b = b)
    (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G) :
    transportCocharacter b a ha G (transportCocharacter b c hc G χ) =
      transportCocharacter b (a ≫ c) (by rw [Category.assoc, hc, ha]) G χ := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv b G T).injective
  rw [transportCocharacter_points, transportCocharacter_points,
    transportCocharacter_points, MulEquiv.apply_symm_apply]
  let e : (Over.map (a ≫ c)).obj T ≅ (Over.map c).obj ((Over.map a).obj T) :=
    Over.isoMk (Iso.refl _) (by simp)
  have hx : e.hom ≫ (Gm.pointsEquiv S ((Over.map c).obj ((Over.map a).obj T))).symm
      (Gm.pointsEquiv S T x) =
        (Gm.pointsEquiv S ((Over.map (a ≫ c)).obj T)).symm (Gm.pointsEquiv S T x) := by
    apply (Gm.pointsEquiv S ((Over.map (a ≫ c)).obj T)).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    change Units.map (𝟙 T.left : T.left ⟶ T.left).appTop.hom.toMonoidHom _ = _
    simp
  have he : (descentTestIso b a ha T).hom ≫
      (descentTestIso b c hc ((Over.map a).obj T)).hom =
        (descentTestIso b (a ≫ c) (by rw [Category.assoc, hc, ha]) T).hom ≫
          (Over.map b).map e.hom := by
    apply Over.OverMorphism.ext
    rfl
  rw [← Category.assoc, he, Category.assoc, ← baseChangePointsEquiv_naturality]
  simp only [← Category.assoc, hx]

/-- Points over the base of a pullback are precisely points of the original group over that base. -/
def baseChangeBasePointsEquiv :
    (Over.mk (𝟙 S) ⟶ ((Over.pullback b).mapGrp.obj G).X) ≃* (Over.mk b ⟶ G.X) :=
  (baseChangePointsEquiv b G (Over.mk (𝟙 S))).trans
    (G.points.mapIso
      (Over.isoMk (Iso.refl S) (by simp) :
        Over.mk b ≅ (Over.map b).obj (Over.mk (𝟙 S))).op).groupIsoToMulEquiv

/-- The comparison of base points is the usual projection from the pullback scheme. -/
theorem baseChangeBasePointsEquiv_left
    (x : Over.mk (𝟙 S) ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    (baseChangeBasePointsEquiv b G x).left = x.left ≫ pullback.fst G.X.hom b := by
  change 𝟙 S ≫ (x.left ≫ pullback.fst G.X.hom b) = _
  exact Category.id_comp _

end Langlands.GroupScheme
