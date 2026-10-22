import Mathlib.Algebra.Group.Hom.Instances
import Langlands.VirtualRepresentation.Supercuspidal.Basic
import Langlands.Representation.Classification.SupercuspidalTwist

/-!
# Actual determinant-character twists on the supercuspidal lattice

Each rank has an open-kernel character trivial on the determinant kernel.
The genuine class twist is invertible, and finite-support reindexing extends
it to the integral lattice. Canonical p-adic real powers are concrete examples.
-/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.Supercuspidal

variable {F : Type uF} [Field F] [TopologicalSpace F]

omit [TopologicalSpace F] in
private theorem ker_inv {n : ℕ} (χ : GeneralLinear n F →* ℂˣ) :
    (χ⁻¹).ker = χ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]

private theorem open_ker_one (n : ℕ) :
    IsOpen ((1 : GeneralLinear n F →* ℂˣ).ker : Set (GeneralLinear n F)) := by
  simp

/-- The actual class twist, with inverse the inverse-character twist. -/
def twistClassEquiv {n : ℕ} (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (GeneralLinear.determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker) :
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F) (n := n) ≃
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F) (n := n) where
  toFun := GeneralLinear.SupercuspidalClass.twist χ hχ hdet
  invFun := GeneralLinear.SupercuspidalClass.twist χ⁻¹
    (by simpa only [ker_inv] using hχ) (by simpa only [ker_inv] using hdet)
  left_inv a := by
    have hc : χ⁻¹ * χ = 1 := by ext g; simp
    have ho : IsOpen ((χ⁻¹ * χ).ker : Set (GeneralLinear n F)) := by
      simpa only [hc] using open_ker_one (F := F) n
    rw [GeneralLinear.SupercuspidalClass.twist_twist _ _ _ _ ho]
    simp only [hc]
    exact GeneralLinear.SupercuspidalClass.twist_one _ a
  right_inv a := by
    have hc : χ * χ⁻¹ = 1 := by ext g; simp
    have ho : IsOpen ((χ * χ⁻¹).ker : Set (GeneralLinear n F)) := by
      simpa only [hc] using open_ker_one (F := F) n
    rw [GeneralLinear.SupercuspidalClass.twist_twist _ _ _ _ ho]
    simp only [hc]
    exact GeneralLinear.SupercuspidalClass.twist_one _ a

section Family

variable (χ : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdet : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤
      (χ n).ker)

/-- Twist the genuine supercuspidal class in each positive group rank. -/
def twistBasisEquiv : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  Equiv.sigmaCongrRight (fun n => twistClassEquiv (χ n) (hχ n) (hdet n))

@[simp]
theorem twistBasisEquiv_rank (b : Basis.{uF, uV} F) :
    (twistBasisEquiv χ hχ hdet b).1 = b.1 := rfl

/-- The underlying smooth dual class is twisted by the same character. -/
@[simp]
theorem underlyingClass_twistBasisEquiv (b : Basis.{uF, uV} F) :
    underlyingClass F (twistBasisEquiv χ hχ hdet b) =
      SmoothDualClass.twist (χ b.1) (hχ b.1) (underlyingClass F b) :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist _ _ _ _

/-- On actual objects this is exactly the published supercuspidal twist. -/
@[simp]
theorem twistBasisEquiv_basisClass (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ))) :
    twistBasisEquiv χ hχ hdet (basisClass n A) =
      basisClass n (GeneralLinear.SupercuspidalRep.twist (χ n) (hχ n) (hdet n) A) := rfl

/-- Extend actual twisting by integral linearity. -/
def twistLatticeEquiv : Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  reindex (twistBasisEquiv χ hχ hdet)

@[simp]
theorem twistLatticeEquiv_single (b : Basis.{uF, uV} F) (m : ℤ) :
    twistLatticeEquiv χ hχ hdet (Finsupp.single b m) =
      Finsupp.single (twistBasisEquiv χ hχ hdet b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem twistLatticeEquiv_generator (b : Basis.{uF, uV} F) :
    twistLatticeEquiv χ hχ hdet (generator b) =
      generator (twistBasisEquiv χ hχ hdet b) :=
  twistLatticeEquiv_single χ hχ hdet b 1

@[simp]
theorem twistLatticeEquiv_coefficient (x : Lattice.{uF, uV} F) (b : Basis.{uF, uV} F) :
    twistLatticeEquiv χ hχ hdet x (twistBasisEquiv χ hχ hdet b) = x b := by
  change x ((twistBasisEquiv χ hχ hdet).symm (twistBasisEquiv χ hχ hdet b)) = x b
  exact congrArg x ((twistBasisEquiv χ hχ hdet).symm_apply_apply b)

@[simp]
theorem degree_twistLatticeEquiv (x : Lattice.{uF, uV} F) :
    degree F (twistLatticeEquiv χ hχ hdet x) = degree F x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [degree, rankedDegree, VirtualRepresentation.degree, extend]

/-- The integral coefficient pairing is unchanged by simultaneous twisting. -/
theorem multiplicityPairing_twistLatticeEquiv (x y : Lattice.{uF, uV} F) :
    multiplicityPairing F (twistLatticeEquiv χ hχ hdet x) (twistLatticeEquiv χ hχ hdet y) =
      multiplicityPairing F x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m => simp [multiplicityPairing, pairing, extend, coefficient]

/-- Reindexing preserves and reflects nonnegative integral coefficients. -/
theorem effective_twistLatticeEquiv_iff (x : Lattice.{uF, uV} F) :
    twistLatticeEquiv χ hχ hdet x ∈ effective F ↔ x ∈ effective F := by
  change (∀ b, 0 ≤ twistLatticeEquiv χ hχ hdet x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (twistBasisEquiv χ hχ hdet b)
  · intro h b
    obtain ⟨a, rfl⟩ := (twistBasisEquiv χ hχ hdet).surjective b
    simpa using h a

@[simp]
theorem twistBasisEquiv_symm :
    (twistBasisEquiv.{uF, uV} χ hχ hdet).symm =
      twistBasisEquiv (fun n => (χ n)⁻¹)
        (fun n => by simpa only [ker_inv] using hχ n)
        (fun n => by simpa only [ker_inv] using hdet n) := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  rfl

@[simp]
theorem twistLatticeEquiv_symm :
    (twistLatticeEquiv.{uF, uV} χ hχ hdet).symm =
      twistLatticeEquiv (fun n => (χ n)⁻¹)
        (fun n => by simpa only [ker_inv] using hχ n)
        (fun n => by simpa only [ker_inv] using hdet n) := by
  simp [twistLatticeEquiv, reindex]

end Family

@[simp]
theorem twistBasisEquiv_one :
    twistBasisEquiv (F := F) (fun _ => 1) (fun n => open_ker_one n)
        (fun _ => GeneralLinear.ker_determinant_le_ker_one) =
      Equiv.refl (Basis.{uF, uV} F) := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  exact congrArg (Sigma.mk n) (GeneralLinear.SupercuspidalClass.twist_one _ b)

@[simp]
theorem twistLatticeEquiv_one :
    twistLatticeEquiv (F := F) (fun _ => 1) (fun n => open_ker_one n)
        (fun _ => GeneralLinear.ker_determinant_le_ker_one) =
      LinearEquiv.refl ℤ (Lattice.{uF, uV} F) := by
  simp [twistLatticeEquiv, reindex]

/-- Compose rank-wise character twists. Openness of the product kernel is explicit. -/
theorem twistBasisEquiv_mul
    (χ η : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hη : ∀ n : ℕ+, IsOpen ((η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hχη : ∀ n : ℕ+, IsOpen ((χ n * η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdetχ : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (χ n).ker)
    (hdetη : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (η n).ker) :
    (twistBasisEquiv.{uF, uV} η hη hdetη).trans (twistBasisEquiv χ hχ hdetχ) =
      twistBasisEquiv (fun n => χ n * η n) hχη
        (fun n => GeneralLinear.ker_determinant_le_ker_mul (hdetχ n) (hdetη n)) := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  exact congrArg (Sigma.mk n)
    (GeneralLinear.SupercuspidalClass.twist_twist _ _ _ _ (hχη n) (hdetχ n) (hdetη n) b)

theorem twistLatticeEquiv_mul
    (χ η : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hη : ∀ n : ℕ+, IsOpen ((η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hχη : ∀ n : ℕ+, IsOpen ((χ n * η n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdetχ : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (χ n).ker)
    (hdetη : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (η n).ker) :
    (twistLatticeEquiv.{uF, uV} η hη hdetη).trans (twistLatticeEquiv χ hχ hdetχ) =
      twistLatticeEquiv (fun n => χ n * η n) hχη
        (fun n => GeneralLinear.ker_determinant_le_ker_mul (hdetχ n) (hdetη n)) := by
  simp only [twistLatticeEquiv, reindex, Finsupp.domLCongr_trans]
  rw [twistBasisEquiv_mul χ η hχ hη hχη hdetχ hdetη]

end Langlands.VirtualRepresentation.Supercuspidal

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Twist by the actual normalized determinant absolute value to a real power. -/
def realPowerTwistBasisEquiv (s : ℝ) : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.twistBasisEquiv
    (fun n => F.canonicalTopologicalData.determinantPowerCharacter n s)
    (fun n => F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter n s)
    (fun n => F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter n s)

@[simp]
theorem realPowerTwistBasisEquiv_rank (s : ℝ) (b : Basis.{uF, uV} F) :
    (realPowerTwistBasisEquiv F s b).1 = b.1 := rfl

@[simp]
theorem realPowerTwistBasisEquiv_zero :
    realPowerTwistBasisEquiv F 0 = Equiv.refl (Basis.{uF, uV} F) := by
  let := F.canonicalTopologicalData.topology
  simp [realPowerTwistBasisEquiv, PadicField.TopologicalData.determinantPowerCharacter]

/-- Successive normalized twists add their real exponents. -/
theorem realPowerTwistBasisEquiv_add (s t : ℝ) :
    (realPowerTwistBasisEquiv.{uF, uV} F t).trans (realPowerTwistBasisEquiv F s) =
      realPowerTwistBasisEquiv F (s + t) := by
  let := F.canonicalTopologicalData.topology
  let T := F.canonicalTopologicalData
  apply Equiv.ext
  rintro ⟨n, b⟩
  have ho : IsOpen (((T.determinantPowerCharacter n s) *
      (T.determinantPowerCharacter n t)).ker : Set (GeneralLinear (n : ℕ) F.Carrier)) := by
    simpa only [PadicField.TopologicalData.determinantPowerCharacter,
      realPowerCharacter_add] using T.isOpen_ker_determinantPowerCharacter n (s + t)
  apply congrArg (Sigma.mk n)
  change GeneralLinear.SupercuspidalClass.twist (T.determinantPowerCharacter n s)
    (T.isOpen_ker_determinantPowerCharacter n s)
    (T.ker_determinant_le_ker_determinantPowerCharacter n s)
    (GeneralLinear.SupercuspidalClass.twist (T.determinantPowerCharacter n t)
      (T.isOpen_ker_determinantPowerCharacter n t)
      (T.ker_determinant_le_ker_determinantPowerCharacter n t) b) =
    GeneralLinear.SupercuspidalClass.twist (T.determinantPowerCharacter n (s + t))
      (T.isOpen_ker_determinantPowerCharacter n (s + t))
      (T.ker_determinant_le_ker_determinantPowerCharacter n (s + t)) b
  simpa only [PadicField.TopologicalData.determinantPowerCharacter, realPowerCharacter_add]
    using GeneralLinear.SupercuspidalClass.twist_twist
      (T.determinantPowerCharacter n s) (T.determinantPowerCharacter n t)
      (T.isOpen_ker_determinantPowerCharacter n s)
      (T.isOpen_ker_determinantPowerCharacter n t) ho
      (T.ker_determinant_le_ker_determinantPowerCharacter n s)
      (T.ker_determinant_le_ker_determinantPowerCharacter n t) b

@[simp]
theorem realPowerTwistBasisEquiv_symm (s : ℝ) :
    (realPowerTwistBasisEquiv.{uF, uV} F s).symm = realPowerTwistBasisEquiv F (-s) := by
  let := F.canonicalTopologicalData.topology
  simp only [realPowerTwistBasisEquiv, Supercuspidal.twistBasisEquiv_symm,
    PadicField.TopologicalData.determinantPowerCharacter, realPowerCharacter_neg]

/-- The canonical integer-linear extension of `|det|^s` twisting. -/
def realPowerTwistLatticeEquiv (s : ℝ) : Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  reindex (realPowerTwistBasisEquiv F s)

@[simp]
theorem realPowerTwistLatticeEquiv_zero :
    realPowerTwistLatticeEquiv F 0 = LinearEquiv.refl ℤ (Lattice.{uF, uV} F) := by
  simp [realPowerTwistLatticeEquiv, reindex]

theorem realPowerTwistLatticeEquiv_add (s t : ℝ) :
    (realPowerTwistLatticeEquiv.{uF, uV} F t).trans (realPowerTwistLatticeEquiv F s) =
      realPowerTwistLatticeEquiv F (s + t) := by
  simp only [realPowerTwistLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    realPowerTwistBasisEquiv_add]

@[simp]
theorem realPowerTwistLatticeEquiv_symm (s : ℝ) :
    (realPowerTwistLatticeEquiv.{uF, uV} F s).symm = realPowerTwistLatticeEquiv F (-s) := by
  simp [realPowerTwistLatticeEquiv, reindex]

@[simp]
theorem realPowerTwistLatticeEquiv_single (s : ℝ) (b : Basis.{uF, uV} F) (m : ℤ) :
    realPowerTwistLatticeEquiv F s (Finsupp.single b m) =
      Finsupp.single (realPowerTwistBasisEquiv F s b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem realPowerTwistLatticeEquiv_generator (s : ℝ) (b : Basis.{uF, uV} F) :
    realPowerTwistLatticeEquiv F s (generator b) =
      generator (realPowerTwistBasisEquiv F s b) :=
  realPowerTwistLatticeEquiv_single F s b 1

@[simp]
theorem realPowerTwistLatticeEquiv_coefficient (s : ℝ) (x : Lattice.{uF, uV} F)
    (b : Basis.{uF, uV} F) :
    realPowerTwistLatticeEquiv F s x (realPowerTwistBasisEquiv F s b) = x b := by
  change x ((realPowerTwistBasisEquiv F s).symm (realPowerTwistBasisEquiv F s b)) = x b
  exact congrArg x ((realPowerTwistBasisEquiv F s).symm_apply_apply b)

@[simp]
theorem degree_realPowerTwistLatticeEquiv (s : ℝ) (x : Lattice.{uF, uV} F) :
    degree F (realPowerTwistLatticeEquiv F s x) = degree F x := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.degree_twistLatticeEquiv _ _ _ x

/-- The coefficient pairing is invariant under the canonical real-power twist. -/
theorem pairing_realPowerTwistLatticeEquiv (s : ℝ) (x y : Lattice.{uF, uV} F) :
    pairing (realPowerTwistLatticeEquiv F s x) (realPowerTwistLatticeEquiv F s y) =
      pairing x y := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.multiplicityPairing_twistLatticeEquiv _ _ _ x y

/-- Real-power twisting preserves and reflects the effective cone. -/
theorem effective_realPowerTwistLatticeEquiv_iff (s : ℝ) (x : Lattice.{uF, uV} F) :
    realPowerTwistLatticeEquiv F s x ∈ effective ↔ x ∈ effective := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.effective_twistLatticeEquiv_iff _ _ _ x

end Langlands.VirtualRepresentation.PadicSupercuspidal
