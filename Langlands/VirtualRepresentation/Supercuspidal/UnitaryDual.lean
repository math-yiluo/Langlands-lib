import Langlands.VirtualRepresentation.Supercuspidal.Dual
import Langlands.VirtualRepresentation.Supercuspidal.Unramified
import Langlands.Representation.Unitary.ConjugateEquiv
import Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement

/-!
# Smooth duality on the actual unitary supercuspidal lattice

The closure and admissible Hermitian-identification statements are explicit
proof inputs. Their consequences restrict the actual smooth dual to the
unitary subset, and then extend it by integral reindexing.
-/

noncomputable section

universe uF uV

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The admissible Hermitian-identification clause transports actual positive
invariant forms to the smooth dual. -/
theorem isUnitarizable_smoothContragredient
    (hHerm : Classification.UnitaryAdmissibleHermitianClause.{uF, uV} F T)
    (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      IsAdmissible A.representation → IsUnitarizable A.representation →
        IsUnitarizable (smoothContragredient A.representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A hA ⟨b⟩
  obtain ⟨E, he, _⟩ := hHerm n hn A hA b
  exact (isUnitarizable_iff_of_conjugateEquiv E he).mp ⟨b⟩

/-- Under the two stated theorem inputs, the actual class contragredient
preserves and reflects unitarizability. -/
theorem isUnitarizable_supercuspidalClassContragredient_iff
    (hsc : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV})
    (hHerm : Classification.UnitaryAdmissibleHermitianClause.{uF, uV} F T)
    (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    ∀ a : GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n),
      GeneralLinear.SupercuspidalClass.IsUnitarizable
          (T.supercuspidalClassContragredient hsc n a) ↔
        GeneralLinear.SupercuspidalClass.IsUnitarizable a := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  have hd (a : GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
      GeneralLinear.SupercuspidalClass.IsUnitarizable a →
        GeneralLinear.SupercuspidalClass.IsUnitarizable
          (T.supercuspidalClassContragredient hsc n a) := by
    induction a using Quotient.inductionOn with
    | h A =>
      exact T.isUnitarizable_smoothContragredient hHerm n hn A.obj A.property.2.1
  intro a
  constructor
  · intro ha
    have hb := hd (T.supercuspidalClassContragredient hsc n a) ha
    simpa only [T.supercuspidalClassContragredient_involutive hsc n a] using hb
  · exact hd a

end Langlands.PadicField.TopologicalData

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (hsc : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV})
    (hHerm : Classification.UnitaryAdmissibleHermitianClause.{uF, uV}
      F F.canonicalTopologicalData)

include hHerm in
/-- The actual smooth dual preserves and reflects the genuine unitary subset. -/
theorem isUnitaryClass_dualBasisEquiv_iff (b : Basis.{uF, uV} F) :
    letI := F.canonicalTopologicalData.topology
    Supercuspidal.IsUnitaryClass F.Carrier (dualBasisEquiv F hsc b) ↔
      Supercuspidal.IsUnitaryClass F.Carrier b :=
  F.canonicalTopologicalData.isUnitarizable_supercuspidalClassContragredient_iff
    hsc hHerm b.1 b.1.pos b.2

/-- Restrict the actual p-adic contragredient involution to unitary classes. -/
def unitaryDualBasisEquiv : UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  (dualBasisEquiv F hsc).subtypeEquiv
    (fun b => (isUnitaryClass_dualBasisEquiv_iff F hsc hHerm b).symm)

@[simp]
theorem unitaryDualBasisEquiv_val (b : UnitaryBasis.{uF, uV} F) :
    (unitaryDualBasisEquiv F hsc hHerm b).val = dualBasisEquiv F hsc b.val := rfl

@[simp]
theorem unitaryDualBasisEquiv_rank (b : UnitaryBasis.{uF, uV} F) :
    (unitaryDualBasisEquiv F hsc hHerm b).val.1 = b.val.1 := rfl

/-- On an actual supercuspidal object the restriction is its smooth dual. -/
@[simp]
theorem unitaryDualBasisEquiv_unitaryBasisClass (n : ℕ+) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    ∀ (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (n : ℕ)))
      (hA : Langlands.IsUnitarizable A.obj.representation),
      unitaryDualBasisEquiv F hsc hHerm (Supercuspidal.unitaryBasisClass n A hA) =
        Supercuspidal.unitaryBasisClass n
          (GeneralLinear.SupercuspidalRep.contragredient
            (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n)
            (F.canonicalTopologicalData.supercuspidalContragredientClosed hsc n) A)
          (F.canonicalTopologicalData.isUnitarizable_smoothContragredient
            hHerm n n.pos A.obj A.property.2.1 hA) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup n
  intro A hA
  rfl

@[simp]
theorem unitaryDualBasisEquiv_symm :
    (unitaryDualBasisEquiv F hsc hHerm).symm = unitaryDualBasisEquiv F hsc hHerm := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (dualBasisEquiv_symm F hsc) b.val

@[simp]
theorem unitaryDualBasisEquiv_apply_apply (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualBasisEquiv F hsc hHerm (unitaryDualBasisEquiv F hsc hHerm b) = b := by
  apply Subtype.ext
  exact dualBasisEquiv_apply_apply F hsc b.val

@[simp]
theorem unitaryDualBasisEquiv_trans_self :
    (unitaryDualBasisEquiv F hsc hHerm).trans (unitaryDualBasisEquiv F hsc hHerm) =
      Equiv.refl (UnitaryBasis.{uF, uV} F) := by
  apply Equiv.ext
  exact unitaryDualBasisEquiv_apply_apply F hsc hHerm

/-- Integral extension on the actual unitary supercuspidal basis. -/
def unitaryDualLatticeEquiv :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  reindex (unitaryDualBasisEquiv F hsc hHerm)

@[simp]
theorem unitaryDualLatticeEquiv_single (b : UnitaryBasis.{uF, uV} F) (m : ℤ) :
    unitaryDualLatticeEquiv F hsc hHerm (Finsupp.single b m) =
      Finsupp.single (unitaryDualBasisEquiv F hsc hHerm b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem unitaryDualLatticeEquiv_generator (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualLatticeEquiv F hsc hHerm (generator b) =
      generator (unitaryDualBasisEquiv F hsc hHerm b) :=
  unitaryDualLatticeEquiv_single F hsc hHerm b 1

@[simp]
theorem unitaryDualLatticeEquiv_coefficient (x : UnitaryLattice.{uF, uV} F)
    (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualLatticeEquiv F hsc hHerm x (unitaryDualBasisEquiv F hsc hHerm b) = x b := by
  change x ((unitaryDualBasisEquiv F hsc hHerm).symm
    (unitaryDualBasisEquiv F hsc hHerm b)) = x b
  exact congrArg x ((unitaryDualBasisEquiv F hsc hHerm).symm_apply_apply b)

@[simp]
theorem unitaryDualLatticeEquiv_symm :
    (unitaryDualLatticeEquiv F hsc hHerm).symm = unitaryDualLatticeEquiv F hsc hHerm := by
  simp [unitaryDualLatticeEquiv, reindex]

@[simp]
theorem unitaryDualLatticeEquiv_apply_apply (x : UnitaryLattice.{uF, uV} F) :
    unitaryDualLatticeEquiv F hsc hHerm (unitaryDualLatticeEquiv F hsc hHerm x) = x := by
  simpa only [unitaryDualLatticeEquiv_symm] using
    (unitaryDualLatticeEquiv F hsc hHerm).symm_apply_apply x

@[simp]
theorem unitaryDualLatticeEquiv_trans_self :
    (unitaryDualLatticeEquiv F hsc hHerm).trans (unitaryDualLatticeEquiv F hsc hHerm) =
      LinearEquiv.refl ℤ (UnitaryLattice.{uF, uV} F) := by
  simp only [unitaryDualLatticeEquiv, reindex, Finsupp.domLCongr_trans,
    unitaryDualBasisEquiv_trans_self, Finsupp.domLCongr_refl]

/-- The restricted dual agrees with the actual dual in the ambient lattice. -/
@[simp]
theorem includeUnitary_dual (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryDualLatticeEquiv F hsc hHerm x) =
      dualLatticeEquiv F hsc (includeUnitary F x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [includeUnitary, Supercuspidal.includeUnitary, includeSubset, map]

@[simp]
theorem unitaryDegree_dual (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryDualLatticeEquiv F hsc hHerm x) = unitaryDegree F x := by
  simp [unitaryDegree]

/-- Simultaneous duality preserves the coefficient pairing. -/
theorem unitaryPairing_dual (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryDualLatticeEquiv F hsc hHerm x)
      (unitaryDualLatticeEquiv F hsc hHerm y) = unitaryPairing F x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m => simp [unitaryPairing, pairing, extend, coefficient]

/-- The restricted dual preserves and reflects nonnegative coefficients. -/
theorem effective_unitaryDual_iff (x : UnitaryLattice.{uF, uV} F) :
    unitaryDualLatticeEquiv F hsc hHerm x ∈ effective ↔ x ∈ effective := by
  change (∀ b, 0 ≤ unitaryDualLatticeEquiv F hsc hHerm x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (unitaryDualBasisEquiv F hsc hHerm b)
  · intro h b
    obtain ⟨a, rfl⟩ := (unitaryDualBasisEquiv F hsc hHerm).surjective b
    simpa using h a

/-- Actual smooth duality inverts the full complex unramified parameter. -/
theorem dualBasisEquiv_unramifiedTwist (z : ℂˣ) (b : Basis.{uF, uV} F) :
    dualBasisEquiv F hsc (unramifiedTwistBasisEquiv F z b) =
      unramifiedTwistBasisEquiv F z⁻¹ (dualBasisEquiv F hsc b) := by
  let := F.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  let T := F.canonicalTopologicalData
  have hd := Supercuspidal.dualBasisEquiv_twist
    (fun n => GeneralLinear.compactOpen_cofinal F T n)
    (fun n => T.supercuspidalContragredientClosed hsc n)
    (fun n => T.determinantUnramifiedCharacter n z)
    (fun n => T.isOpen_ker_determinantUnramifiedCharacter n z)
    (fun n => T.ker_determinant_le_ker_determinantUnramifiedCharacter n z) b
  simpa only [dualBasisEquiv, unramifiedTwistBasisEquiv,
    PadicField.TopologicalData.determinantUnramifiedCharacter_inv] using hd

theorem dualLatticeEquiv_unramifiedTwist (z : ℂˣ) (x : Lattice.{uF, uV} F) :
    dualLatticeEquiv F hsc (unramifiedTwistLatticeEquiv F z x) =
      unramifiedTwistLatticeEquiv F z⁻¹ (dualLatticeEquiv F hsc x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [dualBasisEquiv_unramifiedTwist]

/-- The inverse-parameter compatibility restricts to genuine unitary classes. -/
theorem unitaryDualBasisEquiv_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (b : UnitaryBasis.{uF, uV} F) :
    unitaryDualBasisEquiv F hsc hHerm (unitaryUnramifiedTwistBasisEquiv F z hz b) =
      unitaryUnramifiedTwistBasisEquiv F z⁻¹ (by simp [hz])
        (unitaryDualBasisEquiv F hsc hHerm b) := by
  apply Subtype.ext
  exact dualBasisEquiv_unramifiedTwist F hsc z b.val

theorem unitaryDualLatticeEquiv_unramifiedTwist (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (x : UnitaryLattice.{uF, uV} F) :
    unitaryDualLatticeEquiv F hsc hHerm (unitaryUnramifiedTwistLatticeEquiv F z hz x) =
      unitaryUnramifiedTwistLatticeEquiv F z⁻¹ (by simp [hz])
        (unitaryDualLatticeEquiv F hsc hHerm x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [unitaryDualBasisEquiv_unramifiedTwist]

end Langlands.VirtualRepresentation.PadicSupercuspidal
