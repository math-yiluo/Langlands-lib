import Langlands.GroupScheme.Descent.DatumRelation
import Langlands.GroupScheme.SubgroupBaseChange

/-! # The actual relative Hom functor of group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} (H G : GroupScheme S)

/-- Actual group-scheme homomorphisms after pullback to a test scheme. -/
abbrev RelativeHom (T : Over S) :=
  (baseChange T.hom).obj H ⟶ (baseChange T.hom).obj G

variable {H G}

/-- The projection between actual base changes induced by a test-scheme map. -/
def baseChangeProj (H : GroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    ((baseChange T'.hom).obj H).X.left ⟶ ((baseChange T.hom).obj H).X.left :=
  pullback.lift (pullback.fst H.X.hom T'.hom)
    (pullback.snd H.X.hom T'.hom ≫ a.left)
    (by rw [pullback.condition, Category.assoc, Over.w a])

@[reassoc (attr := simp)]
theorem baseChangeProj_fst (H : GroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    baseChangeProj H a ≫ pullback.fst H.X.hom T.hom =
      pullback.fst H.X.hom T'.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeProj_snd (H : GroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    baseChangeProj H a ≫ pullback.snd H.X.hom T.hom =
      pullback.snd H.X.hom T'.hom ≫ a.left :=
  pullback.lift_snd _ _ _

@[simp]
theorem baseChangeProj_id (H : GroupScheme S) (T : Over S) :
    baseChangeProj H (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

theorem baseChangeProj_comp (H : GroupScheme S) {T T' T'' : Over S}
    (b : T'' ⟶ T') (a : T' ⟶ T) :
    baseChangeProj H (b ≫ a) = baseChangeProj H b ≫ baseChangeProj H a := by
  apply pullback.hom_ext <;> simp

/-- Pull a family of homomorphisms to a test scheme, using the published actual
pullback-composition and base-map equality comparisons. -/
def evaluate {T T' : Over S} (a : T' ⟶ T) (i : RelativeHom H G T) :
    RelativeHom H G T' :=
  Descent.pullHom a.left (Over.w a) (Over.w a) i

/-- A relative homomorphism is determined by its projection to the original target. -/
theorem relativeHom_ext {T : Over S} {i j : RelativeHom H G T}
    (h : i.hom.hom.left ≫ pullback.fst G.X.hom T.hom =
      j.hom.hom.left ≫ pullback.fst G.X.hom T.hom) : i = j := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w i.hom.hom).trans (Over.w j.hom.hom).symm

/-- Evaluation on the original target is given by the canonical projection
between source base changes and the original family. -/
@[reassoc]
theorem evaluate_fst {T T' : Over S} (a : T' ⟶ T) (i : RelativeHom H G T) :
    (evaluate a i).hom.hom.left ≫ pullback.fst G.X.hom T'.hom =
      baseChangeProj H a ≫ i.hom.hom.left ≫ pullback.fst G.X.hom T.hom := by
  simpa only [evaluate, baseChangeProj, pullback.lift_fst_snd, Category.id_comp] using
    (Descent.pullHom_eval a.left (Over.w a) (Over.w a) i
      (pullback.fst H.X.hom T'.hom) (pullback.snd H.X.hom T'.hom)
      pullback.condition)

@[simp]
theorem evaluate_id {T : Over S} (i : RelativeHom H G T) :
    evaluate (𝟙 T) i = i := by
  apply relativeHom_ext
  rw [evaluate_fst, baseChangeProj_id, Category.id_comp]

/-- Successive test-scheme evaluation equals evaluation along the composite. -/
theorem evaluate_comp {T T' T'' : Over S} (b : T'' ⟶ T') (a : T' ⟶ T)
    (i : RelativeHom H G T) :
    evaluate (b ≫ a) i = evaluate b (evaluate a i) := by
  apply relativeHom_ext
  rw [evaluate_fst, evaluate_fst, baseChangeProj_comp, Category.assoc]
  exact congrArg (baseChangeProj H b ≫ ·) (evaluate_fst a i).symm

/-- The relative Hom presheaf uses actual group-scheme homomorphisms on every
test scheme; restriction is actual pullback. -/
def relativeHomFunctor (H G : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := RelativeHom H G T.unop
  map a := TypeCat.ofHom (evaluate (H := H) (G := G) a.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro i
    exact evaluate_id i
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro i
    exact evaluate_comp b.unop a.unop i

/-- Pullback of a family defines the Yoneda transformation associated to it. -/
def parameterization {M : Over S} (i : RelativeHom H G M) :
    yoneda.obj M ⟶ relativeHomFunctor H G where
  app T := TypeCat.ofHom (fun a : T.unop ⟶ M => evaluate a i)
  naturality T T' a := by
    ext b
    exact evaluate_comp a.unop b i

/-- A family is universal when every actual homomorphism on every test scheme
comes from a unique parameter. -/
def IsUniversal {M : Over S} (i : RelativeHom H G M) : Prop :=
  ∀ T : Over S, Function.Bijective (fun a : T ⟶ M => evaluate a i)

/-- A universal family represents the actual relative Hom presheaf. -/
def universalIso {M : Over S} (i : RelativeHom H G M) (hi : IsUniversal i) :
    yoneda.obj M ≅ relativeHomFunctor H G :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Equiv.ofBijective _ (hi T.unop)))
    (fun f => (parameterization i).naturality f)

/-- Every homomorphism is the evaluation of a universal family at a unique
actual morphism of test schemes. -/
theorem IsUniversal.existsUnique {M T : Over S} {i : RelativeHom H G M}
    (hi : IsUniversal i) (j : RelativeHom H G T) :
    ∃! a : T ⟶ M, evaluate a i = j := by
  obtain ⟨a, ha⟩ := (hi T).surjective j
  exact ⟨a, ha, fun b hb => (hi T).injective (hb.trans ha.symm)⟩

/-- Closed immersion of a family persists after evaluation on any test scheme. -/
theorem isClosedImmersion_evaluate {T T' : Over S} (a : T' ⟶ T)
    (i : RelativeHom H G T) (hi : IsClosedImmersion i.hom.hom.left) :
    IsClosedImmersion (evaluate a i).hom.hom.left := by
  have hmap : IsClosedImmersion ((baseChange a.left).map i).hom.hom.left :=
    IsClosedSubgroup.baseChange a.left hi
  change IsClosedImmersion
    ((Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) H).inv.hom.hom.left ≫
      ((baseChange a.left).map i).hom.hom.left ≫
      (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) G).hom.hom.hom.left)
  infer_instance

end Langlands.GroupScheme.HomScheme
