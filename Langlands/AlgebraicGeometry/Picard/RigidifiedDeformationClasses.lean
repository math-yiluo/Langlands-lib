import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationH1
import Langlands.AlgebraicGeometry.Picard.RigidifiedDualNumber
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso

/-! # Rigidified and ordinary actual first-order deformation classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

namespace LineBundle

variable {Y Z : Scheme.{u}}

/-- Pullback along an actual scheme isomorphism on actual line-bundle classes. -/
def classPullbackEquiv (e : Y ≅ Z) :
    IsoClasses preservation Z ≃* IsoClasses preservation Y where
  toFun := pullbackHom preservation e.hom
  invFun := pullbackHom preservation e.inv
  left_inv q := by
    rw [pullbackHom_comp_eq preservation e.inv e.hom e.inv_hom_id, pullbackHom_id]
  right_inv q := by
    rw [pullbackHom_comp_eq preservation e.hom e.inv e.hom_inv_id, pullbackHom_id]
  map_mul' := map_mul _

end LineBundle

namespace RigidifiedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)

/-- Forget the rigidification on actual relative isomorphism classes. -/
def forgetClass (T : Over S) :
    Classes f ε hε T → LineBundle.IsoClasses preservation ((relativeSpace f).obj T) :=
  Quotient.map (forget ((relativeSection f ε hε).app T)).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(forget _).mapIso e⟩)

@[simp]
lemma forgetClass_classOf (T : Over S) (L : relative f ε hε T) :
    forgetClass preservation f ε hε T (classOf f ε hε L) =
      LineBundle.isoClass preservation ((forget _).obj L) := rfl

/-- The retraction of the relative section corrects every underlying isomorphism. -/
lemma forgetClass_injective (T : Over S) :
    Function.Injective (forgetClass preservation f ε hε T) := by
  intro q r
  induction q using Quotient.inductionOn with | h L => ?_
  induction r using Quotient.inductionOn with | h M => ?_
  intro h
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp h
  exact Quotient.sound
    (nonempty_iso_of_forget_iso preservation ((relativeProjection f).app T)
      (relativeSection_projection f ε hε T) e)

/-- Every line bundle can be rigidified over a test scheme with exactly one point. -/
lemma forgetClass_surjective (T : Over S) [Unique T.left] :
    Function.Surjective (forgetClass preservation f ε hε T) := by
  intro q
  induction q using LineBundle.IsoClasses.ind with | h L => ?_
  let : Unique ((Over.forget S).obj T) := inferInstanceAs (Unique T.left)
  obtain ⟨e⟩ := LineBundle.nonempty_iso_trivial_of_unique
    ((LineBundle.pullback ((relativeSection f ε hε).app T)).obj L)
  exact ⟨classOf f ε hε
    (ofLineBundle L (((LineBundle.forget T.left).mapIso e).symm)), rfl⟩

/-- For one-point test schemes forgetting rigidification is a bijection of actual classes. -/
def forgetClassEquiv (T : Over S) [Unique T.left] :
    Classes f ε hε T ≃ LineBundle.IsoClasses preservation ((relativeSpace f).obj T) :=
  Equiv.ofBijective _ ⟨forgetClass_injective preservation f ε hε T,
    forgetClass_surjective preservation f ε hε T⟩

@[simp]
lemma forgetClass_pullback {T U : Over S} (h : T ⟶ U)
    (q : Classes f ε hε U) :
    forgetClass preservation f ε hε T (classesPullback f ε hε h q) =
      LineBundle.pullbackHom preservation ((relativeSpace f).map h)
        (forgetClass preservation f ε hε U q) := by
  induction q using Quotient.inductionOn with | h L => rfl

@[simp]
lemma forgetClass_trivial (T : Over S) :
    forgetClass preservation f ε hε T (classOf f ε hε (relativeTrivial f ε hε T)) = 1 :=
  rfl

/-- Forgetting rigidification preserves the actual tensor operation. -/
lemma forgetClass_tensor (T : Over S) (q r : Classes f ε hε T) :
    forgetClass preservation f ε hε T (classesTensor preservation f ε hε T q r) =
      forgetClass preservation f ε hε T q * forgetClass preservation f ε hε T r := by
  induction q using Quotient.inductionOn with | h L => ?_
  induction r using Quotient.inductionOn with | h M => rfl

end RigidifiedLineBundle

namespace DualNumberThickening

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The base member of the relative family is the original scheme. -/
def baseRelativeIso : X ≅ (relativeSpace f).obj (Over.mk (𝟙 _)) where
  hom := pullback.lift f (𝟙 X) (by simp)
  inv := pullback.snd _ _
  hom_inv_id := pullback.lift_snd _ _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact pullback.condition.symm.trans (Category.comp_id _)
    · simp

/-- The relative augmentation agrees with the actual zero section after the two canonical
fibre-product identifications. -/
lemma baseRelativeIso_augmentation :
    (baseRelativeIso f).hom ≫ (relativeSpace f).map (dualNumberClosedPoint k) =
      closedPoint f ≫ (relativeSpaceSymmetry f (dualNumberTest k)).inv := by
  apply pullback.hom_ext
  · simp [baseRelativeIso, relativeSpace, Over.pullback, dualNumberClosedPoint,
      relativeSpaceSymmetry]
    exact (closedPoint_structure f).symm
  · simp [baseRelativeIso, relativeSpace, Over.pullback, relativeSpaceSymmetry]
    exact (closedPoint_projection f).symm

end DualNumberThickening

variable (k : Type u) [Field k]

/-- The actual dual-number test scheme over a field has exactly one point. -/
instance dualNumberTest_unique : Unique (dualNumberTest k).left where
  default := dualNumberAugmentation k default
  uniq x := by
    obtain ⟨y, rfl⟩ := (dualNumberAugmentation k).surjective x
    exact congrArg (dualNumberAugmentation k) (Subsingleton.elim y default)

namespace RigidifiedLineBundle

open DualNumberThickening

variable {k} {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)

/-- Forget rigidification and identify the relative fibre product with the actual
dual-number thickening. This equivalence is defined on all classes. -/
def underlyingDualNumberClassEquiv :
    Classes f ε hε (dualNumberTest k) ≃
      LineBundle.IsoClasses preservation (thickening f) :=
  (forgetClassEquiv preservation f ε hε (dualNumberTest k)).trans
    (LineBundle.classPullbackEquiv preservation
      (relativeSpaceSymmetry f (dualNumberTest k)).symm).toEquiv

@[simp]
lemma underlyingDualNumberClassEquiv_apply (q : Classes f ε hε (dualNumberTest k)) :
    underlyingDualNumberClassEquiv preservation f ε hε q =
      LineBundle.pullbackHom preservation (relativeSpaceSymmetry f (dualNumberTest k)).inv
        (forgetClass preservation f ε hε (dualNumberTest k) q) :=
  rfl

/-- Restriction to the base agrees with actual zero-section pullback under forgetting. -/
lemma underlyingDualNumberClassEquiv_restriction
    (q : Classes f ε hε (dualNumberTest k)) :
    LineBundle.pullbackHom preservation (baseRelativeIso f).hom
        (forgetClass preservation f ε hε (Over.mk (𝟙 _))
          (classesPullback f ε hε (dualNumberClosedPoint k) q)) =
      LineBundle.pullbackHom preservation (closedPoint f)
        (underlyingDualNumberClassEquiv preservation f ε hε q) := by
  rw [forgetClass_pullback, underlyingDualNumberClassEquiv_apply]
  exact (LineBundle.pullbackHom_comp_eq preservation _ _
    (baseRelativeIso_augmentation f) _).trans
      (LineBundle.pullbackHom_comp preservation _ _ _).symm

/-- The rigidified trivial-restriction condition is exactly the ordinary
zero-section kernel condition. -/
lemma underlyingDualNumberClassEquiv_mem_iff
    (q : Classes f ε hε (dualNumberTest k)) :
    classesPullback f ε hε (dualNumberClosedPoint k) q =
        classOf f ε hε (relativeTrivial f ε hε (Over.mk (𝟙 _))) ↔
      underlyingDualNumberClassEquiv preservation f ε hε q ∈
        DeformationClasses preservation f := by
  change _ ↔ LineBundle.pullbackHom preservation (closedPoint f)
    (underlyingDualNumberClassEquiv preservation f ε hε q) = 1
  rw [← underlyingDualNumberClassEquiv_restriction]
  constructor
  · intro h
    rw [h, forgetClass_trivial, map_one]
  · intro h
    apply forgetClass_injective preservation f ε hε (Over.mk (𝟙 _))
    apply (LineBundle.classPullbackEquiv preservation (baseRelativeIso f)).injective
    simpa only [LineBundle.classPullbackEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      forgetClass_trivial, map_one] using h

/-- Actual first-order rigidified classes are actual ordinary deformation classes. -/
def firstOrderDeformationEquiv :
    FirstOrderClasses f ε hε ≃ DeformationClasses preservation f :=
  (underlyingDualNumberClassEquiv preservation f ε hε).subtypeEquiv
    (underlyingDualNumberClassEquiv_mem_iff preservation f ε hε)

@[simp]
lemma firstOrderDeformationEquiv_val (q : FirstOrderClasses f ε hε) :
    (firstOrderDeformationEquiv preservation f ε hε q).val =
      underlyingDualNumberClassEquiv preservation f ε hε q.val :=
  rfl

/-- The full forgetting equivalence carries actual rigidified tensor to ordinary tensor. -/
lemma underlyingDualNumberClassEquiv_tensor
    (q r : Classes f ε hε (dualNumberTest k)) :
    underlyingDualNumberClassEquiv preservation f ε hε
        (classesTensor preservation f ε hε (dualNumberTest k) q r) =
      underlyingDualNumberClassEquiv preservation f ε hε q *
        underlyingDualNumberClassEquiv preservation f ε hε r := by
  simp only [underlyingDualNumberClassEquiv_apply, forgetClass_tensor, map_mul]

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
