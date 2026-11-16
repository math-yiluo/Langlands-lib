import Langlands.GroupScheme.SchemeActionOfPointLaws
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Fibres of invariant scheme morphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ActionFibre

variable {S : Scheme.{u}} {X Q : Over S} (q : X ⟶ Q)
  (s : Over.mk (𝟙 S) ⟶ Q)

/-- The actual scheme fibre over a section of the base. -/
def parameter : Over S :=
  Over.mk (pullback.snd q.left s.left)

/-- The actual morphism from the fibre to its ambient scheme. -/
def projection : parameter q s ⟶ X :=
  Over.homMk (pullback.fst q.left s.left) (by
    change pullback.fst q.left s.left ≫ X.hom = pullback.snd q.left s.left
    rw [← Over.w q, ← Category.assoc, pullback.condition, Category.assoc, Over.w s]
    exact Category.comp_id _)

@[reassoc] theorem projection_comp :
    projection q s ≫ q = toUnit (parameter q s) ≫ s :=
  Over.OverMorphism.ext pullback.condition

/-- A morphism to the fibre is determined by its ambient component. -/
theorem hom_ext {T : Over S} {x y : T ⟶ parameter q s}
    (h : x ≫ projection q s = y ≫ projection q s) : x = y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun f => f.left) h
  · exact (Over.w x).trans (Over.w y).symm

/-- A point of the ambient scheme with the specified class lifts to the fibre. -/
def pointLift {T : Over S} (x : T ⟶ X)
    (hx : x ≫ q = toUnit T ≫ s) : T ⟶ parameter q s :=
  Over.homMk
    (pullback.lift x.left T.hom (congrArg (fun f => f.left) hx))
    (pullback.lift_snd _ _ _)

@[reassoc] theorem pointLift_projection {T : Over S} (x : T ⟶ X)
    (hx : x ≫ q = toUnit T ≫ s) :
    pointLift q s x hx ≫ projection q s = x :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

instance [Flat q.left] : Flat (parameter q s).hom := by
  change Flat (pullback.snd q.left s.left)
  infer_instance

instance [Surjective q.left] : Surjective (parameter q s).hom := by
  change Surjective (pullback.snd q.left s.left)
  infer_instance

instance [QuasiCompact q.left] : QuasiCompact (parameter q s).hom := by
  change QuasiCompact (pullback.snd q.left s.left)
  infer_instance

variable (A : GroupScheme S) [ModObj A.X X]
  (hinv : ∀ (T : Over S) (a : T ⟶ A.X) (x : T ⟶ X),
    (a • x) ≫ q = x ≫ q)

/-- The ambient action lifts to one actual morphism on the fibre. -/
def actionHom : A.X ⊗ parameter q s ⟶ parameter q s :=
  pointLift q s ((fst _ _) • ((snd _ _) ≫ projection q s)) (by
    rw [hinv, Category.assoc, projection_comp, comp_toUnit_assoc])

@[reassoc] theorem actionHom_projection :
    actionHom q s A hinv ≫ projection q s =
      (fst A.X (parameter q s)) • ((snd A.X (parameter q s)) ≫ projection q s) :=
  pointLift_projection q s _ _

/-- Evaluation of the lifted action agrees with the ambient action. -/
theorem actionHom_eval {T : Over S} (a : T ⟶ A.X)
    (x : T ⟶ parameter q s) :
    (lift a x ≫ actionHom q s A hinv) ≫ projection q s = a • (x ≫ projection q s) := by
  rw [Category.assoc, actionHom_projection, ModObj.comp_smul, lift_fst,
    ← Category.assoc, lift_snd]

/-- The fibre inherits a lawful categorical action from the ambient scheme. -/
@[instance_reducible]
def modObj : ModObj A.X (parameter q s) :=
  schemeActionOfPointLaws (actionHom q s A hinv)
    (fun x => by
      apply hom_ext q s
      rw [actionHom_eval, one_smul])
    (fun a b x => by
      apply hom_ext q s
      rw [actionHom_eval, actionHom_eval, actionHom_eval, mul_smul])

theorem smul_projection {T : Over S} (a : T ⟶ A.X) (x : T ⟶ parameter q s) :
    letI := modObj q s A hinv
    (a • x) ≫ projection q s = a • (x ≫ projection q s) :=
  actionHom_eval q s A hinv a x

/-- Unique differences in each ambient class give an invertible shear on the fibre. -/
theorem leftSMul_isIso
    (horbit : ∀ (T : Over S) (x y : T ⟶ X), x ≫ q = y ≫ q →
      ∃! (a : T ⟶ A.X), a • x = y) :
    letI := modObj q s A hinv
    IsIso (ModObj.leftSMul A.X (parameter q s)) := by
  let := modObj q s A hinv
  apply ModObj.isIso_leftSMul_iff.mpr
  intro T x y
  have hxy : (x ≫ projection q s) ≫ q = (y ≫ projection q s) ≫ q := by
    rw [Category.assoc, Category.assoc, projection_comp, comp_toUnit_assoc, comp_toUnit_assoc]
  obtain ⟨a, ha, hu⟩ := horbit T (x ≫ projection q s) (y ≫ projection q s) hxy
  refine ⟨a, ?_, ?_⟩
  · apply hom_ext q s
    exact (smul_projection q s A hinv a x).trans ha
  · intro b hb
    apply hu b
    exact (smul_projection q s A hinv b x).symm.trans
      (congrArg (fun z => z ≫ projection q s) hb)

end Langlands.GroupScheme.ActionFibre
