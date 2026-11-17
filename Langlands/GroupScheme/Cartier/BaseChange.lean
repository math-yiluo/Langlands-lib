import Langlands.GroupScheme.Cartier.Characters
import Langlands.GroupScheme.Cartier.RelativeHomFunctoriality
import Langlands.GroupScheme.Cartier.RelativeHomPostcompose
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Base change of actual relative homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Cartier

variable {S S' : Scheme.{u}}

/-- Composite and iterated pullback of a commutative group scheme. -/
def testBaseChangeAlongIso (G : CommGroupScheme S) (b : S' ⟶ S) (T : Over S') :
    testBaseChange ((Over.map b).obj T) G ≅
      testBaseChange T ((CommGroupScheme.baseChange b).obj G) where
  hom := Additive.ofMul (Langlands.GroupScheme.baseChangeCompIso b T.hom G.toGrp).hom
  inv := Additive.ofMul (Langlands.GroupScheme.baseChangeCompIso b T.hom G.toGrp).inv
  hom_inv_id := congrArg Additive.ofMul
    (Langlands.GroupScheme.baseChangeCompIso b T.hom G.toGrp).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul
    (Langlands.GroupScheme.baseChangeCompIso b T.hom G.toGrp).inv_hom_id

@[reassoc (attr := simp)]
lemma testBaseChangeAlongIso_inv_fst (G : CommGroupScheme S) (b : S' ⟶ S)
    (T : Over S') :
    CommGroupScheme.hom (testBaseChangeAlongIso G b T).inv ≫
        pullback.fst G.X.hom (T.hom ≫ b) =
      pullback.fst (pullback.snd G.X.hom b) T.hom ≫ pullback.fst G.X.hom b :=
  Langlands.GroupScheme.baseChangeCompIso_inv_fst b T.hom G.toGrp

@[reassoc (attr := simp)]
lemma testBaseChangeAlongIso_hom_fst_fst (G : CommGroupScheme S) (b : S' ⟶ S)
    (T : Over S') :
    CommGroupScheme.hom (testBaseChangeAlongIso G b T).hom ≫
        pullback.fst (pullback.snd G.X.hom b) T.hom ≫ pullback.fst G.X.hom b =
      pullback.fst G.X.hom (T.hom ≫ b) := by
  rw [← testBaseChangeAlongIso_inv_fst]
  change ((testBaseChangeAlongIso G b T).hom ≫
    (testBaseChangeAlongIso G b T).inv).toMul.hom.hom.left ≫ _ = _
  rw [Iso.hom_inv_id]
  exact Category.id_comp _

@[reassoc (attr := simp)]
lemma testBaseChangeAlongIso_inv_snd (G : CommGroupScheme S) (b : S' ⟶ S)
    (T : Over S') :
    CommGroupScheme.hom (testBaseChangeAlongIso G b T).inv ≫
        pullback.snd G.X.hom (T.hom ≫ b) =
      pullback.snd (pullback.snd G.X.hom b) T.hom :=
  Over.w (testBaseChangeAlongIso G b T).inv.toMul.hom.hom

/-- The canonical comparison is natural in the test scheme on first projections. -/
@[reassoc]
lemma testBaseChangeAlongIso_inv_baseChangeProj (G : CommGroupScheme S)
    (b : S' ⟶ S) {T T' : Over S'} (a : T' ⟶ T) :
    CommGroupScheme.hom (testBaseChangeAlongIso G b T').inv ≫
        baseChangeProj G ((Over.map b).map a) =
      baseChangeProj ((CommGroupScheme.baseChange b).obj G) a ≫
        CommGroupScheme.hom (testBaseChangeAlongIso G b T).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeProj, pullback.lift_fst,
      Over.map_obj_hom, testBaseChangeAlongIso_inv_fst]
    change _ = pullback.lift
      (pullback.fst (pullback.snd G.X.hom b) T'.hom)
      (pullback.snd (pullback.snd G.X.hom b) T'.hom ≫ a.left) _ ≫
      pullback.fst (pullback.snd G.X.hom b) T.hom ≫ pullback.fst G.X.hom b
    simp
  · simp only [Category.assoc, baseChangeProj, pullback.lift_snd,
      Over.map_obj_hom, Over.map_map_left, testBaseChangeAlongIso_inv_snd,
      testBaseChangeAlongIso_inv_snd_assoc]
    change _ = pullback.lift
      (pullback.fst (pullback.snd G.X.hom b) T'.hom)
      (pullback.snd (pullback.snd G.X.hom b) T'.hom ≫ a.left) _ ≫
      pullback.snd (pullback.snd G.X.hom b) T.hom
    simp

/-- Pullback composition transports actual relative homomorphisms additively. -/
def relativeHomBaseChangeEquiv (G H : CommGroupScheme S) (b : S' ⟶ S)
    (T : Over S') :
    RelativeHom G H ((Over.map b).obj T) ≃+
      RelativeHom ((CommGroupScheme.baseChange b).obj G)
        ((CommGroupScheme.baseChange b).obj H) T where
  toFun χ := (testBaseChangeAlongIso G b T).inv ≫ χ ≫
    (testBaseChangeAlongIso H b T).hom
  invFun χ := (testBaseChangeAlongIso G b T).hom ≫ χ ≫
    (testBaseChangeAlongIso H b T).inv
  left_inv χ := by simp
  right_inv χ := by simp
  map_add' χ ψ := by simp only [Preadditive.comp_add, Preadditive.add_comp]

@[reassoc]
lemma relativeHomBaseChangeEquiv_fst_fst (G H : CommGroupScheme S) (b : S' ⟶ S)
    (T : Over S') (χ : RelativeHom G H ((Over.map b).obj T)) :
    CommGroupScheme.hom (relativeHomBaseChangeEquiv G H b T χ) ≫
        pullback.fst (pullback.snd H.X.hom b) T.hom ≫ pullback.fst H.X.hom b =
      CommGroupScheme.hom (testBaseChangeAlongIso G b T).inv ≫
        CommGroupScheme.hom χ ≫ pullback.fst H.X.hom (T.hom ≫ b) := by
  simp only [relativeHomBaseChangeEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    CommGroupScheme.hom_comp, Category.assoc]
  exact congrArg (CommGroupScheme.hom (testBaseChangeAlongIso G b T).inv ≫
    CommGroupScheme.hom χ ≫ ·) (testBaseChangeAlongIso_hom_fst_fst H b T)

/-- The base-change comparison respects restriction of actual homomorphisms. -/
lemma relativeHomBaseChangeEquiv_restrict (G H : CommGroupScheme S) (b : S' ⟶ S)
    {T T' : Over S'} (a : T' ⟶ T)
    (χ : RelativeHom G H ((Over.map b).obj T)) :
    relativeHomBaseChangeEquiv G H b T'
        (restrict G H ((Over.map b).map a) χ) =
      restrict ((CommGroupScheme.baseChange b).obj G)
        ((CommGroupScheme.baseChange b).obj H) a
        (relativeHomBaseChangeEquiv G H b T χ) := by
  apply relativeHom_ext
  apply pullback.hom_ext
  · change CommGroupScheme.hom
        (relativeHomBaseChangeEquiv G H b T'
          (restrict G H ((Over.map b).map a) χ)) ≫
        pullback.fst (pullback.snd H.X.hom b) T'.hom ≫
          pullback.fst H.X.hom b = _
    rw [relativeHomBaseChangeEquiv_fst_fst]
    have hr := restrict_fst G H ((Over.map b).map a) χ
    have hp := testBaseChangeAlongIso_inv_baseChangeProj G b a
    have he := relativeHomBaseChangeEquiv_fst_fst G H b T χ
    have hr' := restrict_fst ((CommGroupScheme.baseChange b).obj G)
      ((CommGroupScheme.baseChange b).obj H) a
      (relativeHomBaseChangeEquiv G H b T χ)
    calc
      _ = CommGroupScheme.hom (testBaseChangeAlongIso G b T').inv ≫
          baseChangeProj G ((Over.map b).map a) ≫ CommGroupScheme.hom χ ≫
          pullback.fst H.X.hom (T.hom ≫ b) :=
        congrArg (CommGroupScheme.hom (testBaseChangeAlongIso G b T').inv ≫ ·) hr
      _ = baseChangeProj ((CommGroupScheme.baseChange b).obj G) a ≫
          CommGroupScheme.hom (testBaseChangeAlongIso G b T).inv ≫
          CommGroupScheme.hom χ ≫ pullback.fst H.X.hom (T.hom ≫ b) := by
        rw [← Category.assoc, hp, Category.assoc]
      _ = baseChangeProj ((CommGroupScheme.baseChange b).obj G) a ≫
          CommGroupScheme.hom (relativeHomBaseChangeEquiv G H b T χ) ≫
          pullback.fst (pullback.snd H.X.hom b) T.hom ≫ pullback.fst H.X.hom b :=
        congrArg (baseChangeProj ((CommGroupScheme.baseChange b).obj G) a ≫ ·) he.symm
      _ = _ := by
        convert (congrArg (· ≫ pullback.fst H.X.hom b) hr').symm using 1
        simp only [Category.assoc]
        rfl
  · change CommGroupScheme.hom
        (relativeHomBaseChangeEquiv G H b T'
          (restrict G H ((Over.map b).map a) χ)) ≫
        pullback.fst (pullback.snd H.X.hom b) T'.hom ≫ pullback.snd H.X.hom b = _
    change _ = CommGroupScheme.hom
        (restrict ((CommGroupScheme.baseChange b).obj G)
          ((CommGroupScheme.baseChange b).obj H) a
          (relativeHomBaseChangeEquiv G H b T χ)) ≫
        pullback.fst (pullback.snd H.X.hom b) T'.hom ≫ pullback.snd H.X.hom b
    rw [pullback.condition]
    have hw₁ := Over.w
      (relativeHomBaseChangeEquiv G H b T'
        (restrict G H ((Over.map b).map a) χ)).toMul.hom.hom
    have hw₂ := Over.w
      (restrict ((CommGroupScheme.baseChange b).obj G)
        ((CommGroupScheme.baseChange b).obj H) a
        (relativeHomBaseChangeEquiv G H b T χ)).toMul.hom.hom
    convert (congrArg (· ≫ T'.hom) hw₁).trans
      (congrArg (· ≫ T'.hom) hw₂).symm using 1 <;>
        simp only [Category.assoc] <;> rfl

/-- Restricting the big relative Hom presheaf is base change of its two groups. -/
def relativeHomBaseChangeIso (G H : CommGroupScheme S) (b : S' ⟶ S) :
    (Over.map b).op ⋙ relativeHomFunctor G H ≅
      relativeHomFunctor ((CommGroupScheme.baseChange b).obj G)
        ((CommGroupScheme.baseChange b).obj H) :=
  NatIso.ofComponents
    (fun T => (relativeHomBaseChangeEquiv G H b T.unop).toAddCommGrpIso)
    (by
      intro T T' a
      ext χ
      exact relativeHomBaseChangeEquiv_restrict G H b a.unop χ)

/-- Relative characters commute with arbitrary change of the base scheme. -/
def charactersBaseChangeIso (G : CommGroupScheme S) (b : S' ⟶ S) :
    (Over.map b).op ⋙ characters G ≅
      characters ((CommGroupScheme.baseChange b).obj G) :=
  relativeHomBaseChangeIso G (Gm S) b ≪≫
    (relativeHomTargetFunctor ((CommGroupScheme.baseChange b).obj G)).mapIso
      (Gm.commBaseChangeIso b)

/-- The character comparison is pullback composition followed by the canonical `Gm` map. -/
lemma charactersBaseChangeIso_hom_app_apply (G : CommGroupScheme S) (b : S' ⟶ S)
    (T : Over S') (χ : (characters G).obj (op ((Over.map b).obj T))) :
    (charactersBaseChangeIso G b).hom.app (op T) χ =
      relativeHomBaseChangeEquiv G (Gm S) b T χ ≫
        (CommGroupScheme.baseChange T.hom).map (Gm.commBaseChangeIso b).hom := rfl

end Langlands.GroupScheme.Cartier
