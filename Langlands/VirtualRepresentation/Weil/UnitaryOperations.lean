import Langlands.VirtualRepresentation.Weil.Twist
import Langlands.VirtualRepresentation.Weil.Dual
import Langlands.Weil.Representation.UnitaryProof

/-! # Genuine operations on the unitary irreducible lattice -/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A modulus-one character twists an actual unitary representative. -/
theorem isUnitaryClass_twistBasisEquiv (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (b : IrreducibleBasis.{uG, uV} G)
    (hb : IsUnitaryClass G b) : IsUnitaryClass G (twistBasisEquiv χ b) := by
  obtain ⟨A, hA, hAb⟩ := hb
  refine ⟨FiniteRepresentation.twist χ.toMonoidHom A,
    (FiniteRepresentation.unitaryTwisting G A χ.toMonoidHom hχ).mpr hA, ?_⟩
  rw [underlyingClass_twistBasisEquiv, ← hAb]
  rfl

/-- The inverse of a modulus-one character is again modulus one. -/
theorem norm_inv_character_eq_one (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (g : G) :
    ‖((χ⁻¹) g : ℂ)‖ = 1 := by
  change ‖(((χ g)⁻¹ : ℂˣ) : ℂ)‖ = 1
  simp [hχ g]

/-- Modulus-one twists preserve and reflect the actual unitary subset. -/
theorem isUnitaryClass_twistBasisEquiv_iff (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (b : IrreducibleBasis.{uG, uV} G) :
    IsUnitaryClass G (twistBasisEquiv χ b) ↔ IsUnitaryClass G b := by
  constructor
  · intro h
    have hi := isUnitaryClass_twistBasisEquiv χ⁻¹ (norm_inv_character_eq_one χ hχ)
      (twistBasisEquiv χ b) h
    rw [← twistBasisEquiv_symm] at hi
    simpa only [Equiv.symm_apply_apply] using hi
  · exact isUnitaryClass_twistBasisEquiv χ hχ b

/-- Restrict the genuine twist equivalence to the specified unitary basis. -/
def unitaryTwistBasisEquiv (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) :
    UnitaryBasis.{uG, uV} G ≃ UnitaryBasis.{uG, uV} G :=
  (twistBasisEquiv χ).subtypeEquiv (fun b =>
    (isUnitaryClass_twistBasisEquiv_iff χ hχ b).symm)

@[simp] theorem unitaryTwistBasisEquiv_val (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (b : UnitaryBasis.{uG, uV} G) :
    (unitaryTwistBasisEquiv χ hχ b).val = twistBasisEquiv χ b.val := rfl

@[simp] theorem unitaryTwistBasisEquiv_rank (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (b : UnitaryBasis.{uG, uV} G) :
    (unitaryTwistBasisEquiv χ hχ b).val.1 = b.val.1 := rfl

@[simp] theorem unitaryTwistBasisEquiv_symm (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) :
    (unitaryTwistBasisEquiv.{uG, uV} χ hχ).symm =
      unitaryTwistBasisEquiv χ⁻¹ (norm_inv_character_eq_one χ hχ) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (twistBasisEquiv_symm χ) b.val

/-- The genuine integer-linear modulus-one twist on the unitary lattice. -/
def unitaryTwistLatticeEquiv (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) :
    UnitaryLattice.{uG, uV} G ≃ₗ[ℤ] UnitaryLattice.{uG, uV} G :=
  reindex (unitaryTwistBasisEquiv χ hχ)

@[simp] theorem unitaryTwistLatticeEquiv_single (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (b : UnitaryBasis.{uG, uV} G) (m : ℤ) :
    unitaryTwistLatticeEquiv χ hχ (Finsupp.single b m) =
      Finsupp.single (unitaryTwistBasisEquiv χ hχ b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp] theorem unitaryTwistLatticeEquiv_generator (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (b : UnitaryBasis.{uG, uV} G) :
    unitaryTwistLatticeEquiv χ hχ (generator b) =
      generator (unitaryTwistBasisEquiv χ hχ b) :=
  unitaryTwistLatticeEquiv_single χ hχ b 1

@[simp] theorem unitaryTwistLatticeEquiv_coefficient (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (x : UnitaryLattice.{uG, uV} G)
    (b : UnitaryBasis.{uG, uV} G) :
    unitaryTwistLatticeEquiv χ hχ x (unitaryTwistBasisEquiv χ hχ b) = x b := by
  change x ((unitaryTwistBasisEquiv χ hχ).symm (unitaryTwistBasisEquiv χ hχ b)) = x b
  rw [Equiv.symm_apply_apply]

@[simp] theorem unitaryTwistLatticeEquiv_symm (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) :
    (unitaryTwistLatticeEquiv.{uG, uV} χ hχ).symm =
      unitaryTwistLatticeEquiv χ⁻¹ (norm_inv_character_eq_one χ hχ) := by
  simp [unitaryTwistLatticeEquiv, reindex]

/-- Inclusion into the full lattice intertwines the two actual twists. -/
@[simp] theorem includeUnitary_twist (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (x : UnitaryLattice.{uG, uV} G) :
    includeUnitary G (unitaryTwistLatticeEquiv χ hχ x) =
      twistLatticeEquiv χ (includeUnitary G x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [includeUnitary, includeSubset, map]

@[simp] theorem unitaryDegree_twist (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (x : UnitaryLattice.{uG, uV} G) :
    unitaryDegree G (unitaryTwistLatticeEquiv χ hχ x) = unitaryDegree G x := by
  simp [unitaryDegree]

theorem unitaryPairing_twist (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (x y : UnitaryLattice.{uG, uV} G) :
    unitaryPairing G (unitaryTwistLatticeEquiv χ hχ x)
      (unitaryTwistLatticeEquiv χ hχ y) = unitaryPairing G x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m => simp [unitaryPairing, pairing, extend, coefficient]

theorem effective_unitaryTwist_iff (χ : G →ₜ* ℂˣ)
    (hχ : ∀ g : G, ‖(χ g : ℂ)‖ = 1) (x : UnitaryLattice.{uG, uV} G) :
    unitaryTwistLatticeEquiv χ hχ x ∈ effective ↔ x ∈ effective := by
  change (∀ b, 0 ≤ unitaryTwistLatticeEquiv χ hχ x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (unitaryTwistBasisEquiv χ hχ b)
  · intro h b
    obtain ⟨a, rfl⟩ := (unitaryTwistBasisEquiv χ hχ).surjective b
    simpa using h a

variable [IsTopologicalGroup G]

/-- The actual dual of a unitary representative gives a unitary class. -/
theorem isUnitaryClass_dualBasisEquiv (b : IrreducibleBasis.{uG, uV} G)
    (hb : IsUnitaryClass G b) : IsUnitaryClass G (dualBasisEquiv b) := by
  obtain ⟨A, hA, hAb⟩ := hb
  refine ⟨FiniteRepresentation.dual A, FiniteRepresentation.isUnitary_dual A hA, ?_⟩
  rw [underlyingClass_dualBasisEquiv, ← hAb]
  rfl

theorem isUnitaryClass_dualBasisEquiv_iff (b : IrreducibleBasis.{uG, uV} G) :
    IsUnitaryClass G (dualBasisEquiv b) ↔ IsUnitaryClass G b := by
  constructor
  · intro h
    simpa using isUnitaryClass_dualBasisEquiv (dualBasisEquiv b) h
  · exact isUnitaryClass_dualBasisEquiv b

/-- Restrict genuine contragredience to the actual unitary basis. -/
def unitaryDualBasisEquiv : UnitaryBasis.{uG, uV} G ≃ UnitaryBasis.{uG, uV} G :=
  dualBasisEquiv.subtypeEquiv (fun b => (isUnitaryClass_dualBasisEquiv_iff b).symm)

@[simp] theorem unitaryDualBasisEquiv_val (b : UnitaryBasis.{uG, uV} G) :
    (unitaryDualBasisEquiv b).val = dualBasisEquiv b.val := rfl

@[simp] theorem unitaryDualBasisEquiv_rank (b : UnitaryBasis.{uG, uV} G) :
    (unitaryDualBasisEquiv b).val.1 = b.val.1 := rfl

@[simp] theorem unitaryDualBasisEquiv_symm :
    (unitaryDualBasisEquiv.{uG, uV} (G := G)).symm = unitaryDualBasisEquiv := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun dualBasisEquiv_symm b.val

@[simp] theorem unitaryDualBasisEquiv_apply_apply (b : UnitaryBasis.{uG, uV} G) :
    unitaryDualBasisEquiv (unitaryDualBasisEquiv b) = b := by
  apply Subtype.ext
  exact dualBasisEquiv_apply_apply b.val

/-- The actual contragredient integer-linear involution on the unitary lattice. -/
def unitaryDualLatticeEquiv : UnitaryLattice.{uG, uV} G ≃ₗ[ℤ] UnitaryLattice.{uG, uV} G :=
  reindex unitaryDualBasisEquiv

@[simp] theorem unitaryDualLatticeEquiv_single (b : UnitaryBasis.{uG, uV} G) (m : ℤ) :
    unitaryDualLatticeEquiv (Finsupp.single b m) =
      Finsupp.single (unitaryDualBasisEquiv b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp] theorem unitaryDualLatticeEquiv_generator (b : UnitaryBasis.{uG, uV} G) :
    unitaryDualLatticeEquiv (generator b) = generator (unitaryDualBasisEquiv b) :=
  unitaryDualLatticeEquiv_single b 1

@[simp] theorem unitaryDualLatticeEquiv_coefficient (x : UnitaryLattice.{uG, uV} G)
    (b : UnitaryBasis.{uG, uV} G) :
    unitaryDualLatticeEquiv x (unitaryDualBasisEquiv b) = x b := by
  change x (unitaryDualBasisEquiv.symm (unitaryDualBasisEquiv b)) = x b
  rw [Equiv.symm_apply_apply]

@[simp] theorem unitaryDualLatticeEquiv_symm :
    (unitaryDualLatticeEquiv.{uG, uV} (G := G)).symm = unitaryDualLatticeEquiv := by
  simp [unitaryDualLatticeEquiv, reindex]

@[simp] theorem unitaryDualLatticeEquiv_apply_apply (x : UnitaryLattice.{uG, uV} G) :
    unitaryDualLatticeEquiv (unitaryDualLatticeEquiv x) = x := by
  simpa only [unitaryDualLatticeEquiv_symm] using
    (unitaryDualLatticeEquiv (G := G)).symm_apply_apply x

/-- Inclusion into the full lattice intertwines actual duality. -/
@[simp] theorem includeUnitary_dual (x : UnitaryLattice.{uG, uV} G) :
    includeUnitary G (unitaryDualLatticeEquiv x) =
      dualLatticeEquiv (includeUnitary G x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [includeUnitary, includeSubset, map]

@[simp] theorem unitaryDegree_dual (x : UnitaryLattice.{uG, uV} G) :
    unitaryDegree G (unitaryDualLatticeEquiv x) = unitaryDegree G x := by
  simp [unitaryDegree]

theorem unitaryPairing_dual (x y : UnitaryLattice.{uG, uV} G) :
    unitaryPairing G (unitaryDualLatticeEquiv x) (unitaryDualLatticeEquiv y) =
      unitaryPairing G x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m => simp [unitaryPairing, pairing, extend, coefficient]

theorem effective_unitaryDual_iff (x : UnitaryLattice.{uG, uV} G) :
    unitaryDualLatticeEquiv x ∈ effective ↔ x ∈ effective := by
  change (∀ b, 0 ≤ unitaryDualLatticeEquiv x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (unitaryDualBasisEquiv b)
  · intro h b
    obtain ⟨a, rfl⟩ := (unitaryDualBasisEquiv (G := G)).surjective b
    simpa using h a

end Langlands.VirtualRepresentation.Weil
