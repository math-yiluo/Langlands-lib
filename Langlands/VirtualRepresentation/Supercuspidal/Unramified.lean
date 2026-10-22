import Langlands.VirtualRepresentation.Supercuspidal.UnitaryTwist
import Langlands.Group.GL.UnramifiedCharacter

/-!
# Full unramified twists of genuine supercuspidal classes

All complex units act through the actual normalized determinant order.
The resulting orbit classes carry a well-defined positive group rank.
-/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Twist by z raised to the normalized order of the actual determinant. -/
def unramifiedTwistBasisEquiv (z : ℂˣ) : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.twistBasisEquiv
    (fun n => F.canonicalTopologicalData.determinantUnramifiedCharacter n z)
    (fun n => F.canonicalTopologicalData.isOpen_ker_determinantUnramifiedCharacter n z)
    (fun n => F.canonicalTopologicalData.ker_determinant_le_ker_determinantUnramifiedCharacter n z)

@[simp]
theorem unramifiedTwistBasisEquiv_rank (z : ℂˣ) (b : Basis.{uF, uV} F) :
    (unramifiedTwistBasisEquiv F z b).1 = b.1 := rfl

@[simp]
theorem unramifiedTwistBasisEquiv_one :
    unramifiedTwistBasisEquiv F 1 = Equiv.refl (Basis.{uF, uV} F) := by
  let := F.canonicalTopologicalData.topology
  simp [unramifiedTwistBasisEquiv]

/-- Successive unramified twists multiply their complex parameters. -/
theorem unramifiedTwistBasisEquiv_mul (z w : ℂˣ) :
    (unramifiedTwistBasisEquiv.{uF, uV} F w).trans (unramifiedTwistBasisEquiv F z) =
      unramifiedTwistBasisEquiv F (z * w) := by
  let := F.canonicalTopologicalData.topology
  let T := F.canonicalTopologicalData
  apply Equiv.ext
  rintro ⟨n, b⟩
  have ho : IsOpen (((T.determinantUnramifiedCharacter n z) *
      (T.determinantUnramifiedCharacter n w)).ker : Set (GeneralLinear (n : ℕ) F.Carrier)) := by
    simpa only [PadicField.TopologicalData.determinantUnramifiedCharacter_mul] using T.isOpen_ker_determinantUnramifiedCharacter n (z * w)
  apply congrArg (Sigma.mk n)
  change GeneralLinear.SupercuspidalClass.twist (T.determinantUnramifiedCharacter n z)
    (T.isOpen_ker_determinantUnramifiedCharacter n z)
    (T.ker_determinant_le_ker_determinantUnramifiedCharacter n z)
    (GeneralLinear.SupercuspidalClass.twist (T.determinantUnramifiedCharacter n w)
      (T.isOpen_ker_determinantUnramifiedCharacter n w)
      (T.ker_determinant_le_ker_determinantUnramifiedCharacter n w) b) =
    GeneralLinear.SupercuspidalClass.twist (T.determinantUnramifiedCharacter n (z * w))
      (T.isOpen_ker_determinantUnramifiedCharacter n (z * w))
      (T.ker_determinant_le_ker_determinantUnramifiedCharacter n (z * w)) b
  simpa only [PadicField.TopologicalData.determinantUnramifiedCharacter_mul]
    using GeneralLinear.SupercuspidalClass.twist_twist
      (T.determinantUnramifiedCharacter n z) (T.determinantUnramifiedCharacter n w)
      (T.isOpen_ker_determinantUnramifiedCharacter n z)
      (T.isOpen_ker_determinantUnramifiedCharacter n w) ho
      (T.ker_determinant_le_ker_determinantUnramifiedCharacter n z)
      (T.ker_determinant_le_ker_determinantUnramifiedCharacter n w) b

@[simp]
theorem unramifiedTwistBasisEquiv_symm (z : ℂˣ) :
    (unramifiedTwistBasisEquiv.{uF, uV} F z).symm = unramifiedTwistBasisEquiv F z⁻¹ := by
  let := F.canonicalTopologicalData.topology
  simp only [unramifiedTwistBasisEquiv, Supercuspidal.twistBasisEquiv_symm,
    PadicField.TopologicalData.determinantUnramifiedCharacter_inv]

/-- The canonical integer-linear extension of the full unramified twist. -/
def unramifiedTwistLatticeEquiv (z : ℂˣ) : Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  reindex (unramifiedTwistBasisEquiv F z)

@[simp]
theorem unramifiedTwistLatticeEquiv_one :
    unramifiedTwistLatticeEquiv F 1 = LinearEquiv.refl ℤ (Lattice.{uF, uV} F) := by
  simp [unramifiedTwistLatticeEquiv, reindex]

theorem unramifiedTwistLatticeEquiv_mul (z w : ℂˣ) :
    (unramifiedTwistLatticeEquiv.{uF, uV} F w).trans (unramifiedTwistLatticeEquiv F z) =
      unramifiedTwistLatticeEquiv F (z * w) := by
  simp only [unramifiedTwistLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    unramifiedTwistBasisEquiv_mul]

@[simp]
theorem unramifiedTwistLatticeEquiv_symm (z : ℂˣ) :
    (unramifiedTwistLatticeEquiv.{uF, uV} F z).symm = unramifiedTwistLatticeEquiv F z⁻¹ := by
  simp [unramifiedTwistLatticeEquiv, reindex]

@[simp]
theorem unramifiedTwistLatticeEquiv_single (z : ℂˣ) (b : Basis.{uF, uV} F) (m : ℤ) :
    unramifiedTwistLatticeEquiv F z (Finsupp.single b m) =
      Finsupp.single (unramifiedTwistBasisEquiv F z b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem unramifiedTwistLatticeEquiv_generator (z : ℂˣ) (b : Basis.{uF, uV} F) :
    unramifiedTwistLatticeEquiv F z (generator b) =
      generator (unramifiedTwistBasisEquiv F z b) :=
  unramifiedTwistLatticeEquiv_single F z b 1

@[simp]
theorem unramifiedTwistLatticeEquiv_coefficient (z : ℂˣ) (x : Lattice.{uF, uV} F)
    (b : Basis.{uF, uV} F) :
    unramifiedTwistLatticeEquiv F z x (unramifiedTwistBasisEquiv F z b) = x b := by
  change x ((unramifiedTwistBasisEquiv F z).symm (unramifiedTwistBasisEquiv F z b)) = x b
  exact congrArg x ((unramifiedTwistBasisEquiv F z).symm_apply_apply b)

@[simp]
theorem degree_unramifiedTwistLatticeEquiv (z : ℂˣ) (x : Lattice.{uF, uV} F) :
    degree F (unramifiedTwistLatticeEquiv F z x) = degree F x := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.degree_twistLatticeEquiv _ _ _ x

/-- The coefficient pairing is invariant under the canonical unramified twist. -/
theorem pairing_unramifiedTwistLatticeEquiv (z : ℂˣ) (x y : Lattice.{uF, uV} F) :
    pairing (unramifiedTwistLatticeEquiv F z x) (unramifiedTwistLatticeEquiv F z y) =
      pairing x y := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.multiplicityPairing_twistLatticeEquiv _ _ _ x y

/-- Unramified twisting preserves and reflects the effective cone. -/
theorem effective_unramifiedTwistLatticeEquiv_iff (z : ℂˣ) (x : Lattice.{uF, uV} F) :
    unramifiedTwistLatticeEquiv F z x ∈ effective ↔ x ∈ effective := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.effective_twistLatticeEquiv_iff _ _ _ x

/-- The existing real-power twist is a member of the full unramified family. -/
theorem realPowerTwistBasisEquiv_eq_unramified (s : ℝ) :
    realPowerTwistBasisEquiv.{uF, uV} F s = unramifiedTwistBasisEquiv F
      (Langlands.realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s
        F.canonicalTopologicalData.uniformizerUnit) := by
  let := F.canonicalTopologicalData.topology
  simp only [realPowerTwistBasisEquiv, unramifiedTwistBasisEquiv,
    PadicField.TopologicalData.determinantPowerCharacter,
    PadicField.TopologicalData.realPowerDeterminant_eq_unramifiedCharacter]

/-- The action by every complex unramified determinant character. -/
@[instance_reducible]
def unramifiedTwistAction : MulAction ℂˣ (Basis.{uF, uV} F) where
  smul z b := unramifiedTwistBasisEquiv F z b
  one_smul b := by
    change unramifiedTwistBasisEquiv F 1 b = b
    rw [unramifiedTwistBasisEquiv_one]
    rfl
  mul_smul z w b := (Equiv.congr_fun (unramifiedTwistBasisEquiv_mul F z w) b).symm

/-- Actual supercuspidal classes modulo all unramified determinant twists. -/
abbrev UnramifiedOrbitClasses :=
  letI := unramifiedTwistAction.{uF, uV} F
  OrbitClasses (ι := Basis.{uF, uV} F) ℂˣ

/-- Send a genuine class to its unramified-twist orbit. -/
def unramifiedOrbitClass (b : Basis.{uF, uV} F) : UnramifiedOrbitClasses.{uF, uV} F :=
  letI := unramifiedTwistAction F
  orbitClass ℂˣ b

/-- Orbit equality means that an actual unramified twist relates the two classes. -/
theorem unramifiedOrbitClass_eq_iff (a b : Basis.{uF, uV} F) :
    unramifiedOrbitClass F a = unramifiedOrbitClass F b ↔
      ∃ z : ℂˣ, unramifiedTwistBasisEquiv F z b = a := by
  let := unramifiedTwistAction.{uF, uV} F
  change Quotient.mk _ a = Quotient.mk _ b ↔ _
  rw [Quotient.eq]
  exact MulAction.mem_orbit_iff

@[simp]
theorem unramifiedOrbitClass_twist (z : ℂˣ) (b : Basis.{uF, uV} F) :
    unramifiedOrbitClass F (unramifiedTwistBasisEquiv F z b) = unramifiedOrbitClass F b :=
  (unramifiedOrbitClass_eq_iff F _ _).mpr ⟨z, rfl⟩

/-- Add integral coefficients within each genuine unramified-twist orbit. -/
def unramifiedOrbitMap :
    Lattice.{uF, uV} F →ₗ[ℤ] IntegralLattice (UnramifiedOrbitClasses.{uF, uV} F) :=
  map (unramifiedOrbitClass F)

@[simp]
theorem unramifiedOrbitMap_single (b : Basis.{uF, uV} F) (m : ℤ) :
    unramifiedOrbitMap F (Finsupp.single b m) = Finsupp.single (unramifiedOrbitClass F b) m := by
  simp [unramifiedOrbitMap, map]

@[simp]
theorem unramifiedOrbitMap_twist (z : ℂˣ) (x : Lattice.{uF, uV} F) :
    unramifiedOrbitMap F (unramifiedTwistLatticeEquiv F z x) = unramifiedOrbitMap F x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp

/-- Positive group rank descends to the genuine orbit quotient. -/
def unramifiedOrbitRank : UnramifiedOrbitClasses.{uF, uV} F → ℕ+ := by
  letI := unramifiedTwistAction.{uF, uV} F
  exact Quotient.lift (fun b : Basis F => b.1) (by
    intro a b hab
    obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp hab
    exact (congrArg Sigma.fst hz).symm)

@[simp]
theorem unramifiedOrbitRank_class (b : Basis.{uF, uV} F) :
    unramifiedOrbitRank F (unramifiedOrbitClass F b) = b.1 := rfl

/-- The actual fixed-rank orbit fiber. No finiteness is built in. -/
def unramifiedOrbitRankStratum (n : ℕ+) : Set (UnramifiedOrbitClasses.{uF, uV} F) :=
  {c | unramifiedOrbitRank F c = n}

/-- Rank-weighted integer degree on the orbit lattice. -/
def unramifiedOrbitDegree : IntegralLattice (UnramifiedOrbitClasses.{uF, uV} F) →ₗ[ℤ] ℤ :=
  VirtualRepresentation.degree (fun c => (unramifiedOrbitRank F c : ℕ))

@[simp]
theorem unramifiedOrbitDegree_map (x : Lattice.{uF, uV} F) :
    unramifiedOrbitDegree F (unramifiedOrbitMap F x) = degree F x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [unramifiedOrbitDegree, degree, Supercuspidal.degree, rankedDegree,
      VirtualRepresentation.degree, extend]

/-- Restrict an actual modulus-one unramified twist to the genuine unitary basis. -/
def unitaryUnramifiedTwistBasisEquiv (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.unitaryTwistBasisEquiv
    (fun n => F.canonicalTopologicalData.determinantUnramifiedCharacter n z)
    (fun n => F.canonicalTopologicalData.isOpen_ker_determinantUnramifiedCharacter n z)
    (fun n => F.canonicalTopologicalData.ker_determinant_le_ker_determinantUnramifiedCharacter n z)
    (fun n => F.canonicalTopologicalData.norm_determinantUnramifiedCharacter n z hz)

@[simp]
theorem unitaryUnramifiedTwistBasisEquiv_val (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (b : UnitaryBasis.{uF, uV} F) :
    (unitaryUnramifiedTwistBasisEquiv F z hz b).val = unramifiedTwistBasisEquiv F z b.val := rfl

@[simp]
theorem unitaryUnramifiedTwistBasisEquiv_one :
    unitaryUnramifiedTwistBasisEquiv F 1 (by simp) =
      Equiv.refl (UnitaryBasis.{uF, uV} F) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (unramifiedTwistBasisEquiv_one F) b.val

theorem unitaryUnramifiedTwistBasisEquiv_mul (z w : ℂˣ)
    (hz : ‖(z : ℂ)‖ = 1) (hw : ‖(w : ℂ)‖ = 1) :
    (unitaryUnramifiedTwistBasisEquiv.{uF, uV} F w hw).trans
      (unitaryUnramifiedTwistBasisEquiv F z hz) =
      unitaryUnramifiedTwistBasisEquiv F (z * w) (by simp [hz, hw]) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (unramifiedTwistBasisEquiv_mul F z w) b.val

@[simp]
theorem unitaryUnramifiedTwistBasisEquiv_symm (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    (unitaryUnramifiedTwistBasisEquiv.{uF, uV} F z hz).symm =
      unitaryUnramifiedTwistBasisEquiv F z⁻¹ (by simp [hz]) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (unramifiedTwistBasisEquiv_symm F z) b.val

/-- Integral unramified twisting on the specified unitary supercuspidal basis. -/
def unitaryUnramifiedTwistLatticeEquiv (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  reindex (unitaryUnramifiedTwistBasisEquiv F z hz)

@[simp]
theorem unitaryUnramifiedTwistLatticeEquiv_single (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (b : UnitaryBasis.{uF, uV} F) (m : ℤ) :
    unitaryUnramifiedTwistLatticeEquiv F z hz (Finsupp.single b m) =
      Finsupp.single (unitaryUnramifiedTwistBasisEquiv F z hz b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem includeUnitary_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryUnramifiedTwistLatticeEquiv F z hz x) =
      unramifiedTwistLatticeEquiv F z (includeUnitary F x) := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.includeUnitary_twist _ _ _ _ x

@[simp]
theorem unitaryDegree_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryUnramifiedTwistLatticeEquiv F z hz x) = unitaryDegree F x := by
  simp [unitaryDegree]

theorem unitaryPairing_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryUnramifiedTwistLatticeEquiv F z hz x)
      (unitaryUnramifiedTwistLatticeEquiv F z hz y) = unitaryPairing F x y := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.unitaryPairing_twist _ _ _ _ x y

@[simp]
theorem unitaryUnramifiedTwistLatticeEquiv_one :
    unitaryUnramifiedTwistLatticeEquiv F 1 (by simp) =
      LinearEquiv.refl ℤ (UnitaryLattice.{uF, uV} F) := by
  simp [unitaryUnramifiedTwistLatticeEquiv, reindex]

theorem unitaryUnramifiedTwistLatticeEquiv_mul (z w : ℂˣ)
    (hz : ‖(z : ℂ)‖ = 1) (hw : ‖(w : ℂ)‖ = 1) :
    (unitaryUnramifiedTwistLatticeEquiv.{uF, uV} F w hw).trans
      (unitaryUnramifiedTwistLatticeEquiv F z hz) =
      unitaryUnramifiedTwistLatticeEquiv F (z * w) (by simp [hz, hw]) := by
  simp only [unitaryUnramifiedTwistLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    unitaryUnramifiedTwistBasisEquiv_mul]

@[simp]
theorem unitaryUnramifiedTwistLatticeEquiv_symm (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    (unitaryUnramifiedTwistLatticeEquiv.{uF, uV} F z hz).symm =
      unitaryUnramifiedTwistLatticeEquiv F z⁻¹ (by simp [hz]) := by
  simp [unitaryUnramifiedTwistLatticeEquiv, reindex]

@[simp]
theorem unitaryUnramifiedTwistLatticeEquiv_coefficient (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) (b : UnitaryBasis.{uF, uV} F) :
    unitaryUnramifiedTwistLatticeEquiv F z hz x (unitaryUnramifiedTwistBasisEquiv F z hz b) =
      x b := by
  change x ((unitaryUnramifiedTwistBasisEquiv F z hz).symm
    (unitaryUnramifiedTwistBasisEquiv F z hz b)) = x b
  exact congrArg x ((unitaryUnramifiedTwistBasisEquiv F z hz).symm_apply_apply b)

theorem effective_unitaryUnramifiedTwist_iff (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) :
    unitaryUnramifiedTwistLatticeEquiv F z hz x ∈ effective ↔ x ∈ effective := by
  let := F.canonicalTopologicalData.topology
  exact Supercuspidal.effective_unitaryTwist_iff _ _ _ _ x

end Langlands.VirtualRepresentation.PadicSupercuspidal
