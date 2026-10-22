import Langlands.VirtualRepresentation.Supercuspidal.Twist
import Langlands.Representation.Unitary.Twist

/-!
# Norm-one twists on the actual unitary supercuspidal lattice

The genuine supercuspidal class twist preserves and reflects the existence of
an invariant positive Hermitian form, including on infinite-dimensional carriers.
-/

noncomputable section

universe uF uV

namespace Langlands.GeneralLinear.SupercuspidalClass

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- Norm-one determinant characters preserve and reflect actual unitarizability. -/
theorem isUnitarizable_twist_iff (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (hu : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    IsUnitarizable (twist χ hχ hdet a) ↔ IsUnitarizable a := by
  induction a using Quotient.inductionOn with
  | h A => exact Langlands.isUnitarizable_twist_iff χ hu A.obj.representation

end Langlands.GeneralLinear.SupercuspidalClass

namespace Langlands.VirtualRepresentation.Supercuspidal

variable {F : Type uF} [Field F] [TopologicalSpace F]

omit [TopologicalSpace F] in
private theorem inv_ker {n : ℕ} (χ : GeneralLinear n F →* ℂˣ) :
    (χ⁻¹).ker = χ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]

omit [TopologicalSpace F] in
private theorem inv_norm_one {n : ℕ} (χ : GeneralLinear n F →* ℂˣ)
    (hu : ∀ g, ‖(χ g : ℂ)‖ = 1) (g : GeneralLinear n F) :
    ‖((χ⁻¹) g : ℂ)‖ = 1 := by
  change ‖(((χ g)⁻¹ : ℂˣ) : ℂ)‖ = 1
  simp [hu g]

section Family

variable (χ : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdet : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤
      (χ n).ker)
    (hu : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(χ n g : ℂ)‖ = 1)

include hu in
/-- Twisting preserves and reflects the genuine unitary subset in every rank. -/
theorem isUnitaryClass_twistBasisEquiv_iff (b : Basis.{uF, uV} F) :
    IsUnitaryClass F (twistBasisEquiv χ hχ hdet b) ↔ IsUnitaryClass F b :=
  GeneralLinear.SupercuspidalClass.isUnitarizable_twist_iff
    (χ b.1) (hχ b.1) (hdet b.1) (hu b.1) b.2

/-- Restrict the actual class twist to the unitary basis, with its actual inverse. -/
def unitaryTwistBasisEquiv : UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  (twistBasisEquiv χ hχ hdet).subtypeEquiv (fun b =>
    (isUnitaryClass_twistBasisEquiv_iff χ hχ hdet hu b).symm)

@[simp]
theorem unitaryTwistBasisEquiv_val (b : UnitaryBasis.{uF, uV} F) :
    (unitaryTwistBasisEquiv χ hχ hdet hu b).val = twistBasisEquiv χ hχ hdet b.val := rfl

@[simp]
theorem unitaryTwistBasisEquiv_rank (b : UnitaryBasis.{uF, uV} F) :
    (unitaryTwistBasisEquiv χ hχ hdet hu b).val.1 = b.val.1 := rfl

/-- On an actual object the restriction uses the same scalar-twisted action. -/
@[simp]
theorem unitaryTwistBasisEquiv_unitaryBasisClass (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ)))
    (hA : Langlands.IsUnitarizable A.obj.representation) :
    unitaryTwistBasisEquiv χ hχ hdet hu (unitaryBasisClass n A hA) =
      unitaryBasisClass n (GeneralLinear.SupercuspidalRep.twist (χ n) (hχ n) (hdet n) A)
        ((Langlands.isUnitarizable_twist_iff (χ n) (hu n) A.obj.representation).mpr hA) := rfl

@[simp]
theorem unitaryTwistBasisEquiv_symm :
    (unitaryTwistBasisEquiv.{uF, uV} χ hχ hdet hu).symm =
      unitaryTwistBasisEquiv (fun n => (χ n)⁻¹)
        (fun n => by simpa only [inv_ker] using hχ n)
        (fun n => by simpa only [inv_ker] using hdet n)
        (fun n => inv_norm_one (χ n) (hu n)) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (twistBasisEquiv_symm χ hχ hdet) b.val

/-- Integral extension on precisely the genuine unitary supercuspidal basis. -/
def unitaryTwistLatticeEquiv :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  reindex (unitaryTwistBasisEquiv χ hχ hdet hu)

@[simp]
theorem unitaryTwistLatticeEquiv_single (b : UnitaryBasis.{uF, uV} F) (m : ℤ) :
    unitaryTwistLatticeEquiv χ hχ hdet hu (Finsupp.single b m) =
      Finsupp.single (unitaryTwistBasisEquiv χ hχ hdet hu b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem unitaryTwistLatticeEquiv_generator (b : UnitaryBasis.{uF, uV} F) :
    unitaryTwistLatticeEquiv χ hχ hdet hu (generator b) =
      generator (unitaryTwistBasisEquiv χ hχ hdet hu b) :=
  unitaryTwistLatticeEquiv_single χ hχ hdet hu b 1

@[simp]
theorem unitaryTwistLatticeEquiv_coefficient (x : UnitaryLattice.{uF, uV} F)
    (b : UnitaryBasis.{uF, uV} F) :
    unitaryTwistLatticeEquiv χ hχ hdet hu x (unitaryTwistBasisEquiv χ hχ hdet hu b) = x b := by
  change x ((unitaryTwistBasisEquiv χ hχ hdet hu).symm
    (unitaryTwistBasisEquiv χ hχ hdet hu b)) = x b
  exact congrArg x ((unitaryTwistBasisEquiv χ hχ hdet hu).symm_apply_apply b)

@[simp]
theorem unitaryTwistLatticeEquiv_symm :
    (unitaryTwistLatticeEquiv.{uF, uV} χ hχ hdet hu).symm =
      unitaryTwistLatticeEquiv (fun n => (χ n)⁻¹)
        (fun n => by simpa only [inv_ker] using hχ n)
        (fun n => by simpa only [inv_ker] using hdet n)
        (fun n => inv_norm_one (χ n) (hu n)) := by
  simp [unitaryTwistLatticeEquiv, reindex]

/-- Inclusion into the full lattice commutes with the actual twist. -/
@[simp]
theorem includeUnitary_twist (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryTwistLatticeEquiv χ hχ hdet hu x) =
      twistLatticeEquiv χ hχ hdet (includeUnitary F x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [includeUnitary, includeSubset, map]

@[simp]
theorem unitaryDegree_twist (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryTwistLatticeEquiv χ hχ hdet hu x) = unitaryDegree F x := by
  simp [unitaryDegree]

/-- Simultaneous twisting preserves the integral coefficient pairing. -/
theorem unitaryPairing_twist (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryTwistLatticeEquiv χ hχ hdet hu x)
      (unitaryTwistLatticeEquiv χ hχ hdet hu y) = unitaryPairing F x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m => simp [unitaryPairing, pairing, extend, coefficient]

/-- Nonnegative coefficients are preserved and reflected. -/
theorem effective_unitaryTwist_iff (x : UnitaryLattice.{uF, uV} F) :
    unitaryTwistLatticeEquiv χ hχ hdet hu x ∈ VirtualRepresentation.effective ↔
      x ∈ VirtualRepresentation.effective := by
  change (∀ b, 0 ≤ unitaryTwistLatticeEquiv χ hχ hdet hu x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (unitaryTwistBasisEquiv χ hχ hdet hu b)
  · intro h b
    obtain ⟨a, rfl⟩ := (unitaryTwistBasisEquiv χ hχ hdet hu).surjective b
    simpa using h a

end Family

@[simp]
theorem unitaryTwistBasisEquiv_one :
    unitaryTwistBasisEquiv (F := F) (fun _ => 1) (fun _ => by simp)
        (fun _ => GeneralLinear.ker_determinant_le_ker_one) (fun _ _ => by simp) =
      Equiv.refl (UnitaryBasis.{uF, uV} F) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun twistBasisEquiv_one b.val

@[simp]
theorem unitaryTwistLatticeEquiv_one :
    unitaryTwistLatticeEquiv (F := F) (fun _ => 1) (fun _ => by simp)
        (fun _ => GeneralLinear.ker_determinant_le_ker_one) (fun _ _ => by simp) =
      LinearEquiv.refl ℤ (UnitaryLattice.{uF, uV} F) := by
  simp [unitaryTwistLatticeEquiv, reindex]

/-- Composition of actual norm-one twists; product-kernel openness is explicit. -/
theorem unitaryTwistBasisEquiv_mul
    (χ η : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hη : ∀ n : ℕ+, IsOpen ((η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hχη : ∀ n : ℕ+, IsOpen ((χ n * η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdetχ : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (χ n).ker)
    (hdetη : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (η n).ker)
    (huχ : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(χ n g : ℂ)‖ = 1)
    (huη : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(η n g : ℂ)‖ = 1) :
    (unitaryTwistBasisEquiv.{uF, uV} η hη hdetη huη).trans
        (unitaryTwistBasisEquiv χ hχ hdetχ huχ) =
      unitaryTwistBasisEquiv (fun n => χ n * η n) hχη
        (fun n => GeneralLinear.ker_determinant_le_ker_mul (hdetχ n) (hdetη n))
        (fun n g => by simp [huχ n g, huη n g]) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (twistBasisEquiv_mul χ η hχ hη hχη hdetχ hdetη) b.val

theorem unitaryTwistLatticeEquiv_mul
    (χ η : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hη : ∀ n : ℕ+, IsOpen ((η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hχη : ∀ n : ℕ+, IsOpen ((χ n * η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdetχ : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (χ n).ker)
    (hdetη : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (η n).ker)
    (huχ : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(χ n g : ℂ)‖ = 1)
    (huη : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(η n g : ℂ)‖ = 1) :
    (unitaryTwistLatticeEquiv.{uF, uV} η hη hdetη huη).trans
        (unitaryTwistLatticeEquiv χ hχ hdetχ huχ) =
      unitaryTwistLatticeEquiv (fun n => χ n * η n) hχη
        (fun n => GeneralLinear.ker_determinant_le_ker_mul (hdetχ n) (hdetη n))
        (fun n g => by simp [huχ n g, huη n g]) := by
  simp only [unitaryTwistLatticeEquiv, reindex, Finsupp.domLCongr_trans]
  rw [unitaryTwistBasisEquiv_mul χ η hχ hη hχη hdetχ hdetη huχ huη]

end Langlands.VirtualRepresentation.Supercuspidal
