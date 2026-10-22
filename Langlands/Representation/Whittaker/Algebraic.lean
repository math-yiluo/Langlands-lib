import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Irreducible

/-!
# Equivariant functionals and their coefficient models

This is the algebraic construction used for Whittaker models, parameterized by
an actual subgroup and its character. The concrete upper-unipotent subgroup and
its additive-character construction are separate inputs.
-/

namespace Langlands.Whittaker

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Right translation on all scalar-valued functions, with independent universes. -/
def rightTranslation (R : Type uR) (G : Type uG) [CommRing R] [Group G] :
    Representation R G (G → R) where
  toFun s :=
    { toFun := fun f g => f (g * s)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f g
    exact congrArg f (mul_one g)
  map_mul' s t := by
    ext f g
    exact congrArg f (mul_assoc g s t).symm

variable (N : Subgroup G) (θ : N →* Rˣ)

/-- Scalar-valued functions transforming by `θ` under left multiplication by `N`.
No support or smoothness condition is imposed at this algebraic stage. -/
def equivariantFunctions : Subrepresentation (rightTranslation R G) where
  toSubmodule :=
    { carrier := {f | ∀ n : N, ∀ g : G, f ((n : G) * g) = (θ n : R) * f g}
      zero_mem' := by simp
      add_mem' := by
        intro f h hf hh n g
        change f ((n : G) * g) + h ((n : G) * g) =
          (θ n : R) * (f g + h g)
        rw [hf n g, hh n g, mul_add]
      smul_mem' := by
        intro a f hf n g
        change a * f ((n : G) * g) = (θ n : R) * (a * f g)
        rw [hf n g, mul_left_comm] }
  apply_mem_toSubmodule := by
    intro s f hf n g
    change f (((n : G) * g) * s) = (θ n : R) * f (g * s)
    rw [mul_assoc]
    exact hf n (g * s)

/-- The restricted right action on the character-equivariant function space. -/
def functionRepresentation :
    Representation R G (equivariantFunctions N θ).toSubmodule :=
  (equivariantFunctions N θ).toRepresentation

/-- The full algebraic space of character-equivariant linear functionals.
No topology is put on the representation module or its algebraic dual. -/
def functionals (ρ : Representation R G V) : Submodule R (Module.Dual R V) where
  carrier := {ℓ | ∀ n : N, ∀ v : V, ℓ (ρ (n : G) v) = (θ n : R) * ℓ v}
  zero_mem' := by simp
  add_mem' := by
    intro ℓ m hℓ hm n v
    change ℓ (ρ (n : G) v) + m (ρ (n : G) v) = (θ n : R) * (ℓ v + m v)
    rw [hℓ n v, hm n v, mul_add]
  smul_mem' := by
    intro a ℓ hℓ n v
    change a * ℓ (ρ (n : G) v) = (θ n : R) * (a * ℓ v)
    rw [hℓ n v, mul_left_comm]

variable {N θ} (ρ : Representation R G V)

/-- The coefficient map associated with an equivariant functional, as an intertwiner.
Its underlying function is the accepted `Langlands.matrixCoefficient`. -/
def coefficientMap (ℓ : functionals N θ ρ) :
    ρ.IntertwiningMap (functionRepresentation N θ) where
  toLinearMap := (matrixCoefficient ρ ℓ.val).codRestrict
    (equivariantFunctions N θ).toSubmodule (by
      intro v n g
      change ℓ.val (ρ ((n : G) * g) v) = (θ n : R) * ℓ.val (ρ g v)
      rw [map_mul, Module.End.mul_apply]
      exact ℓ.property n (ρ g v))
  isIntertwining' s := by
    ext v g
    change ℓ.val (ρ g (ρ s v)) = ℓ.val (ρ (g * s) v)
    rw [map_mul, Module.End.mul_apply]

/-- Evaluation at the identity recovers a functional from an equivariant function map. -/
def evaluationFunctional (f : ρ.IntertwiningMap (functionRepresentation N θ)) :
    functionals N θ ρ :=
  ⟨{ toFun := fun v => (f v).val 1
     map_add' v w := by
       change (f (v + w)).val 1 = (f v).val 1 + (f w).val 1
       rw [map_add]
       rfl
     map_smul' a v := by
       change (f (a • v)).val 1 = a * (f v).val 1
       rw [map_smul]
       rfl },
    by
      intro n v
      change (f (ρ (n : G) v)).val 1 = (θ n : R) * (f v).val 1
      rw [f.isIntertwining]
      change (f v).val (1 * (n : G)) = (θ n : R) * (f v).val 1
      simpa only [one_mul, mul_one] using (f v).property n 1⟩

/-- Algebraic reciprocity between equivariant functionals and coefficient intertwiners.
Both inverse identities are proved by evaluation and the intertwining property. -/
def functionalEquiv :
    functionals N θ ρ ≃ₗ[R] ρ.IntertwiningMap (functionRepresentation N θ) where
  toFun := coefficientMap ρ
  invFun := evaluationFunctional ρ
  left_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (ρ 1 v) = ℓ.val v
    rw [map_one, Module.End.one_apply]
  right_inv f := by
    ext v g
    change (f (ρ g v)).val 1 = (f v).val g
    rw [f.isIntertwining]
    change (f v).val (1 * g) = (f v).val g
    rw [one_mul]
  map_add' ℓ m := by
    ext v g
    rfl
  map_smul' a ℓ := by
    ext v g
    rfl

/-- The coefficient model belonging to a specified equivariant functional:
the actual invariant image, including its inherited action. -/
def coefficientModel (ℓ : functionals N θ ρ) :
    Subrepresentation (functionRepresentation N θ) :=
  (coefficientMap ρ ℓ).range

/-- The representation carried by the coefficient image. -/
def modelRepresentation (ℓ : functionals N θ ρ) :
    Representation R G (coefficientModel ρ ℓ).toSubmodule :=
  (coefficientModel ρ ℓ).toRepresentation

/-- The canonical surjective intertwiner onto the coefficient image. -/
def modelMap (ℓ : functionals N θ ρ) :
    ρ.IntertwiningMap (modelRepresentation ρ ℓ) where
  toLinearMap := (coefficientMap ρ ℓ).toLinearMap.rangeRestrict
  isIntertwining' g := by
    ext v x
    change ℓ.val (ρ x (ρ g v)) = ℓ.val (ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

/-- Surjectivity is intrinsic to the image construction. -/
theorem modelMap_surjective (ℓ : functionals N θ ρ) :
    Function.Surjective (modelMap ρ ℓ) :=
  (coefficientMap ρ ℓ).toLinearMap.surjective_rangeRestrict

/-- A coefficient image of a smooth representation is smooth.
An open subgroup fixing a preimage fixes its coefficient function. -/
theorem model_isSmooth [TopologicalSpace G] (hρ : IsSmooth ρ)
    (ℓ : functionals N θ ρ) :
    IsSmooth (R := R) (G := G) (V := (coefficientModel ρ ℓ).toSubmodule)
      (modelRepresentation ρ ℓ) := by
  intro w
  obtain ⟨v, rfl⟩ := modelMap_surjective ρ ℓ w
  obtain ⟨K, hK⟩ := hρ v
  refine ⟨K, ?_⟩
  change ∀ k : K, modelRepresentation ρ ℓ (k : G) (modelMap ρ ℓ v) = modelMap ρ ℓ v
  intro k
  rw [← (modelMap ρ ℓ).isIntertwining]
  exact congrArg (modelMap ρ ℓ) (hK k)

/-- Existence of a nonzero character-equivariant functional.
For irreducible `GL_n` representations and the standard nondegenerate unipotent
character, this is the functional condition used to define genericity. -/
def HasFunctional : Prop :=
  ∃ ℓ : functionals N θ ρ, ℓ.val ≠ 0

section Field

universe uk

variable {k : Type uk} [Field k] [Module k V]
variable {θk : N →* kˣ} (π : Representation k G V)

/-- For an irreducible representation over a field, a nonzero equivariant
functional realizes the representation as its coefficient image.
This constructs the equivalence; it does not assert uniqueness of the functional. -/
noncomputable def modelEquiv [Representation.IsIrreducible π]
    (ℓ : functionals N θk π) (hℓ : ℓ.val ≠ 0) :
    π.Equiv (modelRepresentation π ℓ) := by
  refine (modelMap π ℓ).ofBijective ⟨?_, modelMap_surjective π ℓ⟩
  rcases Representation.IsIrreducible.injective_or_eq_zero
      (k := k) (V := V) (W := (coefficientModel π ℓ).toSubmodule)
      (ρ := π) (σ := modelRepresentation π ℓ) (modelMap π ℓ) with h | h
  · exact h
  · exfalso
    apply hℓ
    apply LinearMap.ext
    intro v
    change ℓ.val v = 0
    have hv : ((modelMap π ℓ v).val).val 1 = 0 := by
      rw [h]
      rfl
    change ℓ.val (π 1 v) = 0 at hv
    simpa only [map_one, Module.End.one_apply] using hv

end Field

end Langlands.Whittaker
