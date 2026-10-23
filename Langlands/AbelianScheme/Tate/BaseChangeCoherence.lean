import Langlands.AbelianScheme.Tate.RationalBaseChange

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u
namespace Langlands.GroupScheme
variable {S S' S'' : Scheme.{u}}

/-- The standard pullback identity comparison, lifted to group objects. -/
def baseChangeIdIso (G : Grp (Over S)) :
    (Over.pullback (𝟙 S)).mapGrp.obj G ≅ G :=
  (Functor.mapGrpNatIso Over.pullbackId).app G ≪≫ Functor.mapGrpIdIso.app G

/-- The standard pullback composition comparison, lifted to group objects. -/
def baseChangeCompIso (b : S' ⟶ S) (c : S'' ⟶ S') (G : Grp (Over S)) :
    (Over.pullback (c ≫ b)).mapGrp.obj G ≅
      (Over.pullback c).mapGrp.obj ((Over.pullback b).mapGrp.obj G) :=
  (Functor.mapGrpNatIso (Over.pullbackComp c b)).app G ≪≫
    Functor.mapGrpCompIso.app G

@[simp] theorem baseChangeIdIso_hom_left (G : Grp (Over S)) :
    (baseChangeIdIso G).hom.hom.hom.left = pullback.fst G.X.hom (𝟙 S) := by
  simp [baseChangeIdIso, Functor.mapGrpNatIso, Functor.mapGrpIdIso,
    Over.pullbackId, conjugateIsoEquiv]

@[reassoc (attr := simp)] theorem baseChangeCompIso_inv_fst
    (b : S' ⟶ S) (c : S'' ⟶ S') (G : Grp (Over S)) :
    (baseChangeCompIso b c G).inv.hom.hom.left ≫ pullback.fst G.X.hom (c ≫ b) =
      pullback.fst (pullback.snd G.X.hom b) c ≫ pullback.fst G.X.hom b := by
  simp [baseChangeCompIso, Functor.mapGrpNatIso, Functor.mapGrpCompIso,
    Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit_app]

/-- The identity base-change point map is the comparison on the group and test scheme. -/
theorem baseChangePointsEquiv_id (G : Grp (Over S)) (T : Over S)
    (x : T ⟶ ((Over.pullback (𝟙 S)).mapGrp.obj G).X) :
    (Over.mapId S).inv.app T ≫ baseChangePointsEquiv (𝟙 S) G T x =
      x ≫ (baseChangeIdIso G).hom.hom.hom := by
  apply Over.OverMorphism.ext
  change ((Over.mapId S).inv.app T).left ≫ (x.left ≫ pullback.fst G.X.hom (𝟙 S)) =
    x.left ≫ (baseChangeIdIso G).hom.hom.hom.left
  simp

/-- Sequential pullback adjunction agrees with pullback along the composite. -/
theorem baseChangePointsEquiv_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (G : Grp (Over S)) (T : Over S'')
    (x : T ⟶ ((Over.pullback c).mapGrp.obj ((Over.pullback b).mapGrp.obj G)).X) :
    baseChangePointsEquiv b G ((Over.map c).obj T)
        (baseChangePointsEquiv c ((Over.pullback b).mapGrp.obj G) T x) =
      (Over.mapComp c b).inv.app T ≫ baseChangePointsEquiv (c ≫ b) G T
        (x ≫ (baseChangeCompIso b c G).inv.hom.hom) := by
  apply Over.OverMorphism.ext
  change (x.left ≫ pullback.fst (pullback.snd G.X.hom b) c) ≫
      pullback.fst G.X.hom b =
    ((Over.mapComp c b).inv.app T).left ≫
      ((x.left ≫ (baseChangeCompIso b c G).inv.hom.hom.left) ≫
        pullback.fst G.X.hom (c ≫ b))
  simp [Category.assoc]

end Langlands.GroupScheme

namespace Langlands.GroupScheme.Tate
variable {S S' S'' : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- Identity coherence at each actual torsion level. -/
theorem levelBaseChange_id (T : Over S) (n : ℕ)
    (x : Level ((Over.pullback (𝟙 S)).mapGrp.obj G) T n) :
    levelRestrict G ((Over.mapId S).inv.app T) n (levelBaseChange (𝟙 S) G T n x) =
      levelMap T (baseChangeIdIso G).hom n x := by
  apply toSection_injective G T n
  exact baseChangePointsEquiv_id G T (Additive.toMul x).val

/-- Composition coherence at each actual torsion level. -/
theorem levelBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (n : ℕ)
    (x : Level ((Over.pullback c).mapGrp.obj ((Over.pullback b).mapGrp.obj G)) T n) :
    levelBaseChange b G ((Over.map c).obj T) n
        (levelBaseChange c ((Over.pullback b).mapGrp.obj G) T n x) =
      levelRestrict G ((Over.mapComp c b).inv.app T) n
        (levelBaseChange (c ≫ b) G T n (levelMap T (baseChangeCompIso b c G).inv n x)) := by
  apply toSection_injective G ((Over.map b).obj ((Over.map c).obj T)) n
  exact baseChangePointsEquiv_base_comp b c G T (Additive.toMul x).val

/-- Identity coherence for any selected actual integral Tate module. -/
theorem integralBaseChange_id (T : Over S) (P : ℕ → Prop)
    (x : Integral ((Over.pullback (𝟙 S)).mapGrp.obj G) T P) :
    testRestrict G P ((Over.mapId S).inv.app T) (integralBaseChange (𝟙 S) G T P x) =
      map T P (baseChangeIdIso G).hom x := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_id G T n.val (x.val n)

/-- Composition coherence for any selected actual integral Tate module. -/
theorem integralBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (P : ℕ → Prop)
    (x : Integral ((Over.pullback c).mapGrp.obj ((Over.pullback b).mapGrp.obj G)) T P) :
    integralBaseChange b G ((Over.map c).obj T) P
        (integralBaseChange c ((Over.pullback b).mapGrp.obj G) T P x) =
      testRestrict G P ((Over.mapComp c b).inv.app T)
        (integralBaseChange (c ≫ b) G T P (map T P (baseChangeCompIso b c G).inv x)) := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_base_comp G b c T n.val (x.val n)

/-- Identity coherence after rationalization. -/
theorem rationalBaseChange_id (T : Over S) (P : ℕ → Prop)
    (x : Rational ((Over.pullback (𝟙 S)).mapGrp.obj G) T P) :
    rationalTestRestrict G P ((Over.mapId S).inv.app T) (rationalBaseChange (𝟙 S) G T P x) =
      rationalMap T P (baseChangeIdIso G).hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalTestRestrict_tmul, rationalBaseChange_tmul,
      rationalMap_tmul, integralBaseChange_id]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- Composition coherence after rationalization. -/
theorem rationalBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (P : ℕ → Prop)
    (x : Rational ((Over.pullback c).mapGrp.obj ((Over.pullback b).mapGrp.obj G)) T P) :
    rationalBaseChange b G ((Over.map c).obj T) P
        (rationalBaseChange c ((Over.pullback b).mapGrp.obj G) T P x) =
      rationalTestRestrict G P ((Over.mapComp c b).inv.app T)
        (rationalBaseChange (c ≫ b) G T P
          (rationalMap T P (baseChangeCompIso b c G).inv x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalTestRestrict_tmul, rationalBaseChange_tmul,
      rationalMap_tmul, integralBaseChange_base_comp]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

end Langlands.GroupScheme.Tate
