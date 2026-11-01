import Langlands.Representation.IntegerLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Generalized-weight blocks of commuting invertible tuples and their normalization -/

set_option autoImplicit false

universe u

namespace Langlands.IntegerLattice

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ## The block -/

/-- The common maximal generalized eigenspace of the tuple entries for the labels `c`. -/
def generalizedWeightBlock (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) :
    Submodule ℂ V :=
  ⨅ i : Fin d, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)

/-- The block is exactly the inline intersection of maximal generalized eigenspaces. -/
theorem generalizedWeightBlock_eq (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) :
    generalizedWeightBlock A c =
      ⨅ i : Fin d, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ) := rfl

theorem mem_generalizedWeightBlock {A : CommutingInvertibleTuple d V} {c : Fin d → ℂˣ}
    {v : V} :
    v ∈ generalizedWeightBlock A c ↔
      ∀ i : Fin d, v ∈ (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ) :=
  Submodule.mem_iInf _

/-- At rank zero the empty intersection is the whole space. -/
@[simp] theorem generalizedWeightBlock_rank_zero (A : CommutingInvertibleTuple 0 V)
    (c : Fin 0 → ℂˣ) : generalizedWeightBlock A c = ⊤ :=
  iInf_of_empty _

/-! ## Invariance and the restricted representation -/

/-- Every tuple entry commutes with every lattice action, the lattice being abelian. -/
theorem commute_tupleRepresentationEquiv (A : CommutingInvertibleTuple d V) (i : Fin d)
    (n : Lattice d) :
    Commute (A.1 i : Module.End ℂ V) (tupleRepresentationEquiv d V A n) := by
  rw [← tupleRepresentationEquiv_generator]
  exact (Commute.all (generator d i) n).map (tupleRepresentationEquiv d V A)

/-- Every lattice action maps the block into itself. -/
theorem mapsTo_generalizedWeightBlock (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (n : Lattice d) :
    Set.MapsTo (tupleRepresentationEquiv d V A n) (generalizedWeightBlock A c)
      (generalizedWeightBlock A c) := fun _ hv =>
  mem_generalizedWeightBlock.2 fun i =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tupleRepresentationEquiv A i n)
      (c i : ℂ) (mem_generalizedWeightBlock.1 hv i)

/-- The invariance in the form used by `Representation.subrepresentation`. -/
theorem generalizedWeightBlock_le_comap (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (n : Lattice d) :
    generalizedWeightBlock A c ≤
      (generalizedWeightBlock A c).comap (tupleRepresentationEquiv d V A n) :=
  fun _ hv => mapsTo_generalizedWeightBlock A c n hv

/-- The actual restriction of the tuple's lattice representation to the block. -/
def generalizedWeightBlockRepresentation (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) : Representation ℂ (Lattice d) (generalizedWeightBlock A c) :=
  (tupleRepresentationEquiv d V A).subrepresentation (generalizedWeightBlock A c)
    (generalizedWeightBlock_le_comap A c)

/-- The restricted action of every lattice point is the ambient action. -/
@[simp] theorem generalizedWeightBlockRepresentation_apply_coe
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d)
    (w : generalizedWeightBlock A c) :
    ((generalizedWeightBlockRepresentation A c n w : generalizedWeightBlock A c) : V) =
      tupleRepresentationEquiv d V A n (w : V) := rfl

/-- The inverse of the restricted unit at `n` acts as the ambient action at `n⁻¹`. -/
theorem generalizedWeightBlockRepresentation_asGroupHom_inv_apply_coe
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d)
    (w : generalizedWeightBlock A c) :
    (((((generalizedWeightBlockRepresentation A c).asGroupHom n)⁻¹ :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) w : V) =
      tupleRepresentationEquiv d V A n⁻¹ (w : V) := by
  rw [← map_inv, Representation.asGroupHom_apply]
  rfl

/-- The same inverse equation through the ambient inverse unit. -/
theorem generalizedWeightBlockRepresentation_asGroupHom_inv_apply_coe'
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d)
    (w : generalizedWeightBlock A c) :
    (((((generalizedWeightBlockRepresentation A c).asGroupHom n)⁻¹ :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) w : V) =
      (((((tupleRepresentationEquiv d V A).asGroupHom n)⁻¹ : (Module.End ℂ V)ˣ) :
        Module.End ℂ V) (w : V)) := by
  rw [generalizedWeightBlockRepresentation_asGroupHom_inv_apply_coe, ← map_inv,
    Representation.asGroupHom_apply]

/-- The restricted actions at `n⁻¹` and `n` are inverse, on the left. -/
theorem generalizedWeightBlockRepresentation_inv_self_apply
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d)
    (w : generalizedWeightBlock A c) :
    generalizedWeightBlockRepresentation A c n⁻¹ (generalizedWeightBlockRepresentation A c n w) =
      w :=
  (generalizedWeightBlockRepresentation A c).inv_self_apply n w

/-- The restricted actions at `n` and `n⁻¹` are inverse, on the right. -/
theorem generalizedWeightBlockRepresentation_self_inv_apply
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d)
    (w : generalizedWeightBlock A c) :
    generalizedWeightBlockRepresentation A c n (generalizedWeightBlockRepresentation A c n⁻¹ w) =
      w :=
  (generalizedWeightBlockRepresentation A c).self_inv_apply n w

/-- At rank zero the restricted representation is trivial. -/
@[simp] theorem generalizedWeightBlockRepresentation_rank_zero
    (A : CommutingInvertibleTuple 0 V) (c : Fin 0 → ℂˣ) (n : Lattice 0) :
    generalizedWeightBlockRepresentation A c n = 1 := by
  ext w
  simp

/-! ## Block generator units -/

/-- The block generator unit in coordinate `i`: the restricted action of `generator d i`. -/
def generalizedWeightBlockGenerator (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (i : Fin d) : (Module.End ℂ (generalizedWeightBlock A c))ˣ :=
  (generalizedWeightBlockRepresentation A c).asGroupHom (generator d i)

/-- The block generator's underlying map is the restricted action of the generator. -/
theorem coe_generalizedWeightBlockGenerator (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) :
    (generalizedWeightBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) =
      generalizedWeightBlockRepresentation A c (generator d i) :=
  Representation.asGroupHom_apply _ _

/-- The block generator's inverse is the restricted action of the inverse generator. -/
theorem coe_generalizedWeightBlockGenerator_inv (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) :
    (((generalizedWeightBlockGenerator A c i)⁻¹ :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) =
      generalizedWeightBlockRepresentation A c (generator d i)⁻¹ := by
  rw [generalizedWeightBlockGenerator, ← map_inv, Representation.asGroupHom_apply]

/-- In `V`, the block generator acts as the tuple entry `A.1 i`. -/
@[simp] theorem generalizedWeightBlockGenerator_apply_coe
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (i : Fin d)
    (w : generalizedWeightBlock A c) :
    (((generalizedWeightBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) w :
        generalizedWeightBlock A c) : V) =
      (A.1 i : Module.End ℂ V) (w : V) := by
  rw [coe_generalizedWeightBlockGenerator, generalizedWeightBlockRepresentation_apply_coe,
    tupleRepresentationEquiv_generator]

/-- In `V`, the inverse block generator acts as the actual inverse `(A.1 i)⁻¹`. -/
@[simp] theorem generalizedWeightBlockGenerator_inv_apply_coe
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (i : Fin d)
    (w : generalizedWeightBlock A c) :
    (((((generalizedWeightBlockGenerator A c i)⁻¹ :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) w : generalizedWeightBlock A c) : V) =
      ((((A.1 i)⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) (w : V)) := by
  rw [coe_generalizedWeightBlockGenerator_inv, generalizedWeightBlockRepresentation_apply_coe,
    ← Representation.asGroupHom_apply, map_inv, tupleRepresentationEquiv_asGroupHom_generator]

/-! ## The coordinate character -/

/-- The character of the integer lattice with values `c i` at the standard generators. -/
def coordinateCharacter (c : Fin d → ℂˣ) : Lattice d →* ℂˣ where
  toFun n := ∏ i : Fin d, c i ^ n.toAdd i
  map_one' := by simp
  map_mul' m n := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

/-- The product formula, with integer exponents. -/
theorem coordinateCharacter_apply (c : Fin d → ℂˣ) (n : Lattice d) :
    coordinateCharacter c n = ∏ i : Fin d, c i ^ n.toAdd i := rfl

/-- The same formula for the underlying complex number. -/
theorem coe_coordinateCharacter (c : Fin d → ℂˣ) (n : Lattice d) :
    ((coordinateCharacter c n : ℂˣ) : ℂ) = ∏ i : Fin d, (c i : ℂ) ^ n.toAdd i := by
  rw [coordinateCharacter_apply, Units.coe_prod]
  simp only [Units.val_zpow_eq_zpow_val]

/-- The value at the standard generator in coordinate `i` is `c i`. -/
@[simp] theorem coordinateCharacter_generator (c : Fin d → ℂˣ) (i : Fin d) :
    coordinateCharacter c (generator d i) = c i := by
  rw [coordinateCharacter_apply, Finset.prod_eq_single i]
  · simp [generator]
  · intro j _ hj
    simp [generator, Pi.single_eq_of_ne hj]
  · simp

/-- The value at the inverse standard generator is `(c i)⁻¹`. -/
@[simp] theorem coordinateCharacter_generator_inv (c : Fin d → ℂˣ) (i : Fin d) :
    coordinateCharacter c (generator d i)⁻¹ = (c i)⁻¹ := by
  rw [map_inv, coordinateCharacter_generator]

/-- At rank zero the character is the empty product. -/
@[simp] theorem coordinateCharacter_rank_zero (c : Fin 0 → ℂˣ) (n : Lattice 0) :
    coordinateCharacter c n = 1 := by
  simp [coordinateCharacter_apply]

/-! ## Normalized generators and their differences -/

/-- The normalized block generator unit `(c i)⁻¹ • G_i`: the unit image of `(c i)⁻¹` under
the scalar algebra map, multiplied by the block generator. -/
def normalizedBlockGenerator (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (i : Fin d) : (Module.End ℂ (generalizedWeightBlock A c))ˣ :=
  Units.map (algebraMap ℂ (Module.End ℂ (generalizedWeightBlock A c))).toMonoidHom
      (c i)⁻¹ * generalizedWeightBlockGenerator A c i

/-- Forward scalar normalization: `U_i = (c i)⁻¹ • G_i`. -/
theorem coe_normalizedBlockGenerator (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (i : Fin d) :
    (normalizedBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) =
      (c i : ℂ)⁻¹ •
        (generalizedWeightBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) := by
  rw [normalizedBlockGenerator, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Units.val_inv_eq_inv_val, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul]

/-- Inverse scalar normalization: `U_i⁻¹ = c i • G_i⁻¹`. -/
theorem coe_normalizedBlockGenerator_inv (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) :
    (((normalizedBlockGenerator A c i)⁻¹ : (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
        Module.End ℂ (generalizedWeightBlock A c)) =
      (c i : ℂ) •
        (((generalizedWeightBlockGenerator A c i)⁻¹ :
          (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
            Module.End ℂ (generalizedWeightBlock A c)) := by
  rw [normalizedBlockGenerator, mul_inv_rev, Units.val_mul, ← map_inv, inv_inv, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one]

/-- In `V`, the normalized generator acts as `(c i)⁻¹ • A.1 i`. -/
theorem normalizedBlockGenerator_apply_coe (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) (w : generalizedWeightBlock A c) :
    (((normalizedBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) w :
        generalizedWeightBlock A c) : V) =
      (c i : ℂ)⁻¹ • (A.1 i : Module.End ℂ V) (w : V) := by
  rw [coe_normalizedBlockGenerator, LinearMap.smul_apply, Submodule.coe_smul,
    generalizedWeightBlockGenerator_apply_coe]

/-- In `V`, the inverse normalized generator acts as `c i • (A.1 i)⁻¹`. -/
theorem normalizedBlockGenerator_inv_apply_coe (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) (w : generalizedWeightBlock A c) :
    (((((normalizedBlockGenerator A c i)⁻¹ :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) w : generalizedWeightBlock A c) : V) =
      (c i : ℂ) • ((((A.1 i)⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) (w : V)) := by
  rw [coe_normalizedBlockGenerator_inv, LinearMap.smul_apply, Submodule.coe_smul,
    generalizedWeightBlockGenerator_inv_apply_coe]

/-- The difference `N_i = U_i - 1` between the normalized generator and the identity. -/
def normalizedGeneratorDifference (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (i : Fin d) : Module.End ℂ (generalizedWeightBlock A c) :=
  (normalizedBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) - 1

/-- `1 + N_i` is the normalized generator. -/
theorem one_add_normalizedGeneratorDifference (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) :
    1 + normalizedGeneratorDifference A c i =
      (normalizedBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) := by
  rw [normalizedGeneratorDifference, add_sub_cancel]

/-- The normalization identity `G_i = c i • (1 + N_i)`. -/
theorem generalizedWeightBlockGenerator_eq_smul (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) :
    (generalizedWeightBlockGenerator A c i : Module.End ℂ (generalizedWeightBlock A c)) =
      (c i : ℂ) • (1 + normalizedGeneratorDifference A c i) := by
  rw [one_add_normalizedGeneratorDifference, coe_normalizedBlockGenerator, smul_smul,
    mul_inv_cancel₀ (c i).ne_zero, one_smul]

/-- The inverse normalization identity `G_i⁻¹ = (c i)⁻¹ • U_i⁻¹`. -/
theorem coe_generalizedWeightBlockGenerator_inv_eq_smul (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) :
    (((generalizedWeightBlockGenerator A c i)⁻¹ :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) =
      (c i : ℂ)⁻¹ •
        (((normalizedBlockGenerator A c i)⁻¹ : (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) := by
  rw [coe_normalizedBlockGenerator_inv, smul_smul, inv_mul_cancel₀ (c i).ne_zero, one_smul]

/-- In `V`, the difference acts as `(c i)⁻¹ • A.1 i - 1`. -/
theorem normalizedGeneratorDifference_apply_coe (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (i : Fin d) (w : generalizedWeightBlock A c) :
    ((normalizedGeneratorDifference A c i w : generalizedWeightBlock A c) : V) =
      (c i : ℂ)⁻¹ • (A.1 i : Module.End ℂ V) (w : V) - (w : V) := by
  rw [normalizedGeneratorDifference, LinearMap.sub_apply, Submodule.coe_sub,
    normalizedBlockGenerator_apply_coe, Module.End.one_apply]

end Langlands.IntegerLattice
