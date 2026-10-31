import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

/-! # The group of isomorphism classes of line bundles on a scheme -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Isomorphism classes of line bundles on `X`. The tensor-preservation proof is recorded
in the type so that the tensor group structure can be found by instance search. -/
@[nolint unusedArguments]
def IsoClasses (_preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (X : Scheme.{u}) : Type (u + 1) :=
  Quotient (isIsomorphicSetoid (LineBundle X))

variable {preservation}
variable {X Y Z : Scheme.{u}}

/-- The isomorphism class of a line bundle. -/
def isoClass (preservation : pullbackTensorComparisonIsIsoStatement.{u}) (L : LineBundle X) :
    IsoClasses preservation X :=
  Quotient.mk (isIsomorphicSetoid (LineBundle X)) L

lemma isoClass_eq_iff {L M : LineBundle X} :
    isoClass preservation L = isoClass preservation M ↔ Nonempty (L ≅ M) :=
  Quotient.eq (r := isIsomorphicSetoid (LineBundle X))

lemma isoClass_eq_of_iso {L M : LineBundle X} (e : L ≅ M) :
    isoClass preservation L = isoClass preservation M :=
  isoClass_eq_iff.mpr ⟨e⟩

@[elab_as_elim]
lemma IsoClasses.ind {motive : IsoClasses preservation X → Prop}
    (h : ∀ L : LineBundle X, motive (isoClass preservation L)) (q : IsoClasses preservation X) :
    motive q :=
  Quotient.ind h q

variable (preservation)

/-- The explicit associator as an isomorphism of line bundles. -/
def tensorAssocIso (L M N : LineBundle X) :
    tensor preservation (tensor preservation L M) N ≅
      tensor preservation L (tensor preservation M N) :=
  ObjectProperty.isoMk _ (tensorAssociator L.obj M.obj N.obj)

/-- The explicit left unitor as an isomorphism of line bundles. -/
def trivialTensorIso (L : LineBundle X) : tensor preservation (trivial X) L ≅ L :=
  ObjectProperty.isoMk _ (tensorLeftUnitor L.obj)

instance : CommMonoid (IsoClasses preservation X) where
  mul := Quotient.map₂ (tensor preservation)
    (fun _ _ ⟨e⟩ _ _ ⟨d⟩ ↦ ⟨tensorIso preservation e d⟩)
  mul_assoc := by
    intro a b c
    induction a using IsoClasses.ind with | h L => ?_
    induction b using IsoClasses.ind with | h M => ?_
    induction c using IsoClasses.ind with | h N => ?_
    exact isoClass_eq_of_iso (tensorAssocIso preservation L M N)
  one := isoClass preservation (trivial X)
  one_mul := by
    intro a
    induction a using IsoClasses.ind with | h L => ?_
    exact isoClass_eq_of_iso (trivialTensorIso preservation L)
  mul_one := by
    intro a
    induction a using IsoClasses.ind with | h L => ?_
    exact isoClass_eq_of_iso (tensorTrivialIso preservation L)
  mul_comm := by
    intro a b
    induction a using IsoClasses.ind with | h L => ?_
    induction b using IsoClasses.ind with | h M => ?_
    exact isoClass_eq_of_iso (tensorCommIso preservation L M)

lemma isoClass_tensor (L M : LineBundle X) :
    isoClass preservation (tensor preservation L M) =
      isoClass preservation L * isoClass preservation M := rfl

lemma isoClass_trivial : isoClass preservation (trivial X) = 1 := rfl

lemma isUnit_isoClasses (q : IsoClasses preservation X) : IsUnit q := by
  induction q using IsoClasses.ind with | h L => ?_
  obtain ⟨M, ⟨e⟩⟩ := exists_tensorObj_iso_structureSheaf L
  exact isUnit_iff_exists_inv.mpr
    ⟨isoClass preservation M, isoClass_eq_of_iso (ObjectProperty.isoMk _ e)⟩

instance : CommGroup (IsoClasses preservation X) :=
  commGroupOfIsUnit (isUnit_isoClasses preservation)

/-- Pullback of line bundles on isomorphism classes, as a group homomorphism. -/
def pullbackHom (f : X ⟶ Y) : IsoClasses preservation Y →* IsoClasses preservation X where
  toFun := Quotient.map (pullback f).obj (fun _ _ ⟨e⟩ ↦ ⟨(pullback f).mapIso e⟩)
  map_one' := isoClass_eq_of_iso (pullbackTrivialIso f)
  map_mul' := by
    intro a b
    induction a using IsoClasses.ind with | h L => ?_
    induction b using IsoClasses.ind with | h M => ?_
    exact isoClass_eq_of_iso (pullbackTensorObjIso preservation f L M)

@[simp] lemma pullbackHom_isoClass (f : X ⟶ Y) (L : LineBundle Y) :
    pullbackHom preservation f (isoClass preservation L) =
      isoClass preservation ((pullback f).obj L) := rfl

lemma pullbackHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) (q : IsoClasses preservation Z) :
    pullbackHom preservation f (pullbackHom preservation g q) =
      pullbackHom preservation (f ≫ g) q := by
  induction q using IsoClasses.ind with | h L => ?_
  exact isoClass_eq_of_iso ((pullbackComp f g).app L)

lemma pullbackHom_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    (q : IsoClasses preservation Z) :
    pullbackHom preservation f (pullbackHom preservation g q) =
      pullbackHom preservation h q := by
  rw [pullbackHom_comp, w]

lemma pullbackHom_id (q : IsoClasses preservation X) :
    pullbackHom preservation (𝟙 X) q = q := by
  induction q using IsoClasses.ind with | h L => ?_
  exact isoClass_eq_of_iso ((pullbackId X).app L)

/-- On a scheme with one point every class is trivial. -/
lemma isoClasses_eq_one_of_unique [Unique X] (q : IsoClasses preservation X) : q = 1 := by
  induction q using IsoClasses.ind with | h L => ?_
  obtain ⟨e⟩ := nonempty_iso_trivial_of_unique L
  exact isoClass_eq_of_iso e

/-- A class pulled back through a one-point scheme is trivial. -/
lemma pullbackHom_eq_one_of_factor [Unique Y] (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) (q : IsoClasses preservation Z) :
    pullbackHom preservation h q = 1 := by
  rw [← pullbackHom_comp_eq preservation f g w, isoClasses_eq_one_of_unique preservation
    (pullbackHom preservation g q), map_one]

end Langlands.AlgebraicGeometry.Picard.LineBundle
