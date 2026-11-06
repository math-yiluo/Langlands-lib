import Langlands.Algebra.OrderedPBWNormalization
import Langlands.Algebra.OrderedPBWSpanning
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping.PBW

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
variable {n : ℕ} (b : Module.Basis (Fin n) k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Normalize after insertion of a Lie algebra element. -/
def normalAction : L →ₗ[k] Module.End k (WordModule k n) where
  toFun x := (normalForm b).comp (insert b x)
  map_add' x y := by ext p; simp
  map_smul' a x := by ext p; simp

@[simp]
theorem normalAction_apply (x : L) (p : WordModule k n) :
    normalAction b x p = normalForm b (insert b x p) := rfl

/-- The proved normalized commutator identity supplies the Lie law. -/
theorem normalAction_map_lie (x y : L) :
    normalAction b ⁅x, y⁆ = ⁅normalAction b x, normalAction b y⁆ := by
  apply LinearMap.ext
  intro p
  change normalForm b (insert b ⁅x, y⁆ p) =
    normalForm b (insert b x (normalForm b (insert b y p))) -
      normalForm b (insert b y (normalForm b (insert b x p)))
  rw [normalForm_insert_normalForm, normalForm_insert_normalForm]
  exact eq_sub_iff_add_eq.mpr
    ((add_comm _ _).trans (normalForm_insert_pair b x y p).symm)

/-- The Lie action on the formal word module. -/
def lieAction : L →ₗ⁅k⁆ Module.End k (WordModule k n) :=
  { normalAction b with map_lie' := fun {x y} => normalAction_map_lie b x y }

/-- Lift the Lie action to Mathlib's actual universal enveloping algebra. -/
def envelopingAction : UniversalEnvelopingAlgebra k L →ₐ[k] Module.End k (WordModule k n) :=
  UniversalEnvelopingAlgebra.lift k (lieAction b)

@[simp]
theorem envelopingAction_generator (x : L) (p : WordModule k n) :
    envelopingAction b (UniversalEnvelopingAlgebra.ι k x) p =
      normalForm b (insert b x p) := by
  rw [envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- Acting on the empty word evaluates an arbitrary basis word to its normal form. -/
theorem envelopingAction_basisWord (w : List (Fin n)) :
    envelopingAction b (basisWord b w) (Finsupp.single [] 1) =
      normalForm b (Finsupp.single w 1) := by
  induction w with
  | nil =>
    simpa only [basisWord_nil, map_one, Module.End.one_apply] using
      (normalForm_ascending b [] (by simp)).symm
  | cons i w ih =>
    rw [basisWord_cons, map_mul, Module.End.mul_apply, ih,
      envelopingAction_generator, normalForm_insert_normalForm, insert_basis,
      prepend_single]

/-- Coefficients of the action on the empty word, defined on the actual quotient. -/
def coefficientMap : UniversalEnvelopingAlgebra k L →ₗ[k] WordModule k n where
  toFun a := envelopingAction b a (Finsupp.single [] 1)
  map_add' a c := by simp
  map_smul' r a := by simp

/-- Ordered monomials act on the empty word as distinct unit singletons. -/
theorem coefficientMap_orderedPBWMonomial (e : Fin n → ℕ) :
    coefficientMap b (orderedPBWMonomial b e) = Finsupp.single (exponentWord e) 1 := by
  change envelopingAction b (orderedPBWMonomial b e) (Finsupp.single [] 1) = _
  rw [← exponentWord_product b e]
  change envelopingAction b (basisWord b (exponentWord e)) (Finsupp.single [] 1) = _
  rw [envelopingAction_basisWord, normalForm_ascending b _ (exponentWord_pairwise e)]

/-- Independence of the actual ordered monomials, with no extra premise. -/
theorem orderedPBWMonomial_linearIndependent : LinearIndependent k (orderedPBWMonomial b) := by
  have h := (Finsupp.linearIndependent_single_one (ι := List (Fin n)) (R := k)).comp
    exponentWord exponentWord_injective
  apply LinearIndependent.of_comp (coefficientMap b)
  simpa only [Function.comp_def, coefficientMap_orderedPBWMonomial] using h

end Langlands.Algebra.UniversalEnveloping.PBW
