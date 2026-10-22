import Langlands.VirtualRepresentation.Supercuspidal.Twist
import Langlands.Representation.Classification.SupercuspidalContragredient

/-!
# Smooth contragredient on supercuspidal integral lattices

The actual class involution extends by integral reindexing. Compact-open
cofinality and preservation of supercuspidality remain explicit hypotheses.
-/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.Supercuspidal

variable {F : Type uF} [Field F] [TopologicalSpace F]
    [∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F)]
    (hG : ∀ n : ℕ+, CompactOpenCofinal (GeneralLinear (n : ℕ) F))
    (hsc : ∀ n : ℕ+, GeneralLinear.SupercuspidalContragredientClosed.{uF, uV}
      (F := F) (n := (n : ℕ)))

/-- Dualize each genuine supercuspidal class, retaining its positive rank. -/
def dualBasisEquiv : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  Equiv.sigmaCongrRight (fun n =>
    (GeneralLinear.SupercuspidalClass.contragredient_involutive (hG n) (hsc n)).toPerm)

@[simp]
theorem dualBasisEquiv_rank (b : Basis.{uF, uV} F) :
    (dualBasisEquiv hG hsc b).1 = b.1 := rfl

/-- Forgetting supercuspidality recovers the actual smooth-dual class. -/
@[simp]
theorem underlyingClass_dualBasisEquiv (b : Basis.{uF, uV} F) :
    underlyingClass F (dualBasisEquiv hG hsc b) =
      SmoothDualClass.contragredient (hG b.1) (underlyingClass F b) :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass_contragredient _ _ _

@[simp]
theorem dualBasisEquiv_symm :
    (dualBasisEquiv.{uF, uV} hG hsc).symm = dualBasisEquiv hG hsc := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  rfl

@[simp]
theorem dualBasisEquiv_apply_apply (b : Basis.{uF, uV} F) :
    dualBasisEquiv hG hsc (dualBasisEquiv hG hsc b) = b := by
  simpa only [dualBasisEquiv_symm] using
    (dualBasisEquiv hG hsc).symm_apply_apply b

@[simp]
theorem dualBasisEquiv_trans_self :
    (dualBasisEquiv.{uF, uV} hG hsc).trans (dualBasisEquiv hG hsc) =
      Equiv.refl (Basis.{uF, uV} F) := by
  apply Equiv.ext
  exact dualBasisEquiv_apply_apply hG hsc

/-- The basis operation is the actual smooth contragredient on representatives. -/
@[simp]
theorem dualBasisEquiv_basisClass (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ))) :
    dualBasisEquiv hG hsc (basisClass n A) =
      basisClass n (GeneralLinear.SupercuspidalRep.contragredient (hG n) (hsc n) A) := rfl

/-- Extend the genuine dual-class involution by integral linearity. -/
def dualLatticeEquiv :
    Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  reindex (dualBasisEquiv hG hsc)

@[simp]
theorem dualLatticeEquiv_single (b : Basis.{uF, uV} F) (m : ℤ) :
    dualLatticeEquiv hG hsc (Finsupp.single b m) =
      Finsupp.single (dualBasisEquiv hG hsc b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem dualLatticeEquiv_generator (b : Basis.{uF, uV} F) :
    dualLatticeEquiv hG hsc (generator b) = generator (dualBasisEquiv hG hsc b) :=
  dualLatticeEquiv_single hG hsc b 1

/-- The coefficient of the dual class equals the original multiplicity. -/
@[simp]
theorem dualLatticeEquiv_coefficient (x : Lattice.{uF, uV} F)
    (b : Basis.{uF, uV} F) :
    dualLatticeEquiv hG hsc x (dualBasisEquiv hG hsc b) = x b := by
  change x ((dualBasisEquiv hG hsc).symm (dualBasisEquiv hG hsc b)) = x b
  exact congrArg x ((dualBasisEquiv hG hsc).symm_apply_apply b)

@[simp]
theorem dualLatticeEquiv_symm :
    (dualLatticeEquiv.{uF, uV} hG hsc).symm = dualLatticeEquiv hG hsc := by
  simp [dualLatticeEquiv, reindex]

@[simp]
theorem dualLatticeEquiv_apply_apply (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv hG hsc (dualLatticeEquiv hG hsc x) = x := by
  simpa only [dualLatticeEquiv_symm] using
    (dualLatticeEquiv hG hsc).symm_apply_apply x

@[simp]
theorem dualLatticeEquiv_trans_self :
    (dualLatticeEquiv.{uF, uV} hG hsc).trans (dualLatticeEquiv hG hsc) =
      LinearEquiv.refl ℤ (Lattice.{uF, uV} F) := by
  simp only [dualLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    dualBasisEquiv_trans_self, Finsupp.domLCongr_refl]

/-- Duality preserves the rank-weighted integer degree. -/
@[simp]
theorem degree_dualLatticeEquiv (x : Lattice.{uF, uV} F) :
    degree F (dualLatticeEquiv hG hsc x) = degree F x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [degree, rankedDegree, VirtualRepresentation.degree, extend]

/-- Duality preserves the coefficient pairing on the genuine irreducible basis. -/
theorem multiplicityPairing_dualLatticeEquiv
    (x y : Lattice.{uF, uV} F) :
    multiplicityPairing F (dualLatticeEquiv hG hsc x) (dualLatticeEquiv hG hsc y) =
      multiplicityPairing F x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [multiplicityPairing, pairing, extend, coefficient]

/-- Duality preserves and reflects the effective cone. -/
theorem effective_dualLatticeEquiv_iff (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv hG hsc x ∈ VirtualRepresentation.effective ↔
      x ∈ VirtualRepresentation.effective := by
  change (∀ b, 0 ≤ dualLatticeEquiv hG hsc x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (dualBasisEquiv hG hsc b)
  · intro h b
    obtain ⟨a, rfl⟩ := (dualBasisEquiv hG hsc).surjective b
    simpa using h a

/-- Smooth duality converts a genuine determinant-character twist to the inverse twist. -/
theorem dualBasisEquiv_twist
    (χ : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdet : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤
      (χ n).ker) (b : Basis.{uF, uV} F) :
    dualBasisEquiv hG hsc (twistBasisEquiv χ hχ hdet b) =
      twistBasisEquiv (fun n => (χ n)⁻¹)
        (fun n => isOpen_ker_inv (hχ n))
        (fun n => GeneralLinear.ker_determinant_le_ker_inv (hdet n))
        (dualBasisEquiv hG hsc b) := by
  rcases b with ⟨n, b⟩
  exact congrArg (Sigma.mk n)
    (GeneralLinear.SupercuspidalClass.contragredient_twist
      (hG n) (hsc n) (χ n) (hχ n) (hdet n) b)

/-- The inverse-character compatibility extends to every virtual element. -/
theorem dualLatticeEquiv_twist
    (χ : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdet : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤
      (χ n).ker) (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv hG hsc (twistLatticeEquiv χ hχ hdet x) =
      twistLatticeEquiv (fun n => (χ n)⁻¹)
        (fun n => isOpen_ker_inv (hχ n))
        (fun n => GeneralLinear.ker_determinant_le_ker_inv (hdet n))
        (dualLatticeEquiv hG hsc x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [dualBasisEquiv_twist]

end Langlands.VirtualRepresentation.Supercuspidal

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV})

/-- The actual canonical p-adic basis dual, conditional on the published closure target. -/
def dualBasisEquiv : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  letI : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  Supercuspidal.dualBasisEquiv
    (fun n => GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n)
    (fun n => F.canonicalTopologicalData.supercuspidalContragredientClosed h n)

@[simp]
theorem dualBasisEquiv_rank (b : Basis.{uF, uV} F) :
    (dualBasisEquiv F h b).1 = b.1 := rfl

/-- On a fixed rank this is exactly the published canonical class contragredient. -/
@[simp]
theorem dualBasisEquiv_mk (n : ℕ+)
    (a : PadicField.SupercuspidalClass.{uV, uF} F n n.pos) :
    dualBasisEquiv F h ⟨n, a⟩ =
      ⟨n, PadicField.SupercuspidalClass.contragredient h a⟩ := rfl

@[simp]
theorem dualBasisEquiv_symm :
    (dualBasisEquiv F h).symm = dualBasisEquiv F h := by
  let := F.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  exact Supercuspidal.dualBasisEquiv_symm _ _

@[simp]
theorem dualBasisEquiv_apply_apply (b : Basis.{uF, uV} F) :
    dualBasisEquiv F h (dualBasisEquiv F h b) = b := by
  simpa only [dualBasisEquiv_symm] using (dualBasisEquiv F h).symm_apply_apply b

@[simp]
theorem dualBasisEquiv_trans_self :
    (dualBasisEquiv F h).trans (dualBasisEquiv F h) =
      Equiv.refl (Basis.{uF, uV} F) := by
  apply Equiv.ext
  exact dualBasisEquiv_apply_apply F h

/-- The actual smooth dual on the canonical integral lattice, under the same hypothesis. -/
def dualLatticeEquiv : Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  reindex (dualBasisEquiv F h)

@[simp]
theorem dualLatticeEquiv_single (b : Basis.{uF, uV} F) (m : ℤ) :
    dualLatticeEquiv F h (Finsupp.single b m) =
      Finsupp.single (dualBasisEquiv F h b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem dualLatticeEquiv_generator (b : Basis.{uF, uV} F) :
    dualLatticeEquiv F h (generator b) = generator (dualBasisEquiv F h b) :=
  dualLatticeEquiv_single F h b 1

@[simp]
theorem dualLatticeEquiv_coefficient (x : Lattice.{uF, uV} F) (b : Basis.{uF, uV} F) :
    dualLatticeEquiv F h x (dualBasisEquiv F h b) = x b := by
  change x ((dualBasisEquiv F h).symm (dualBasisEquiv F h b)) = x b
  exact congrArg x ((dualBasisEquiv F h).symm_apply_apply b)

@[simp]
theorem dualLatticeEquiv_symm :
    (dualLatticeEquiv F h).symm = dualLatticeEquiv F h := by
  simp [dualLatticeEquiv, reindex]

@[simp]
theorem dualLatticeEquiv_apply_apply (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv F h (dualLatticeEquiv F h x) = x := by
  simpa only [dualLatticeEquiv_symm] using (dualLatticeEquiv F h).symm_apply_apply x

@[simp]
theorem dualLatticeEquiv_trans_self :
    (dualLatticeEquiv F h).trans (dualLatticeEquiv F h) =
      LinearEquiv.refl ℤ (Lattice.{uF, uV} F) := by
  simp only [dualLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    dualBasisEquiv_trans_self, Finsupp.domLCongr_refl]

@[simp]
theorem degree_dualLatticeEquiv (x : Lattice.{uF, uV} F) :
    degree F (dualLatticeEquiv F h x) = degree F x := by
  let := F.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  exact Supercuspidal.degree_dualLatticeEquiv _ _ x

/-- Simultaneous duality preserves the integral coefficient pairing. -/
theorem pairing_dualLatticeEquiv (x y : Lattice.{uF, uV} F) :
    pairing (dualLatticeEquiv F h x) (dualLatticeEquiv F h y) = pairing x y := by
  let := F.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  exact Supercuspidal.multiplicityPairing_dualLatticeEquiv _ _ x y

/-- Canonical smooth duality preserves and reflects effectiveness. -/
theorem effective_dualLatticeEquiv_iff (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv F h x ∈ effective ↔ x ∈ effective := by
  let := F.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  exact Supercuspidal.effective_dualLatticeEquiv_iff _ _ x

/-- Smooth duality negates the exponent of the actual normalized real-power twist. -/
theorem dualBasisEquiv_realPowerTwist (s : ℝ) (b : Basis.{uF, uV} F) :
    dualBasisEquiv F h (realPowerTwistBasisEquiv F s b) =
      realPowerTwistBasisEquiv F (-s) (dualBasisEquiv F h b) := by
  let := F.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  let T := F.canonicalTopologicalData
  have hd := Supercuspidal.dualBasisEquiv_twist
    (fun n => GeneralLinear.compactOpen_cofinal F T n)
    (fun n => T.supercuspidalContragredientClosed h n)
    (fun n => T.determinantPowerCharacter n s)
    (fun n => T.isOpen_ker_determinantPowerCharacter n s)
    (fun n => T.ker_determinant_le_ker_determinantPowerCharacter n s) b
  simpa only [dualBasisEquiv, realPowerTwistBasisEquiv,
    PadicField.TopologicalData.determinantPowerCharacter, realPowerCharacter_neg] using hd

theorem dualLatticeEquiv_realPowerTwist (s : ℝ) (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv F h (realPowerTwistLatticeEquiv F s x) =
      realPowerTwistLatticeEquiv F (-s) (dualLatticeEquiv F h x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [dualBasisEquiv_realPowerTwist]

end Langlands.VirtualRepresentation.PadicSupercuspidal
