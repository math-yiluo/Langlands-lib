import Langlands.VirtualRepresentation.Supercuspidal.UnitaryDual
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Classification.UnitaryAdmissibleHermitianProof

/-!
# Unconditional smooth duality on the p-adic supercuspidal lattices

The published closure and admissible Hermitian-identification theorems supply
the proof inputs of the existing dual constructions. These operations therefore
take only the p-adic field, retaining independent field and carrier universes.
-/

noncomputable section

universe uF uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual smooth contragredient of positive-rank supercuspidal classes. -/
abbrev contragredientBasisEquiv : Basis.{uF, uV} F ≃ Basis.{uF, uV} F :=
  dualBasisEquiv F GeneralLinear.supercuspidalContragredient

@[simp]
theorem contragredientBasisEquiv_rank (b : Basis.{uF, uV} F) :
    (contragredientBasisEquiv F b).1 = b.1 := rfl

/-- The rankwise operation is the actual class smooth contragredient. -/
@[simp]
theorem contragredientBasisEquiv_mk (n : ℕ+)
    (a : PadicField.SupercuspidalClass.{uV, uF} F n n.pos) :
    contragredientBasisEquiv F ⟨n, a⟩ =
      ⟨n, PadicField.SupercuspidalClass.contragredient
        GeneralLinear.supercuspidalContragredient a⟩ := rfl

@[simp]
theorem contragredientBasisEquiv_symm :
    (contragredientBasisEquiv.{uF, uV} F).symm = contragredientBasisEquiv F :=
  dualBasisEquiv_symm F GeneralLinear.supercuspidalContragredient

@[simp]
theorem contragredientBasisEquiv_apply_apply (b : Basis.{uF, uV} F) :
    contragredientBasisEquiv F (contragredientBasisEquiv F b) = b :=
  dualBasisEquiv_apply_apply F GeneralLinear.supercuspidalContragredient b

@[simp]
theorem contragredientBasisEquiv_trans_self :
    (contragredientBasisEquiv.{uF, uV} F).trans (contragredientBasisEquiv F) =
      Equiv.refl (Basis.{uF, uV} F) :=
  dualBasisEquiv_trans_self F GeneralLinear.supercuspidalContragredient

/-- Extend the actual smooth dual to the integral supercuspidal lattice. -/
abbrev contragredientLatticeEquiv : Lattice.{uF, uV} F ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  dualLatticeEquiv F GeneralLinear.supercuspidalContragredient

@[simp]
theorem contragredientLatticeEquiv_single (b : Basis.{uF, uV} F) (m : ℤ) :
    contragredientLatticeEquiv F (Finsupp.single b m) =
      Finsupp.single (contragredientBasisEquiv F b) m :=
  dualLatticeEquiv_single F GeneralLinear.supercuspidalContragredient b m

@[simp]
theorem contragredientLatticeEquiv_generator (b : Basis.{uF, uV} F) :
    contragredientLatticeEquiv F (generator b) =
      generator (contragredientBasisEquiv F b) :=
  dualLatticeEquiv_generator F GeneralLinear.supercuspidalContragredient b

@[simp]
theorem contragredientLatticeEquiv_coefficient
    (x : Lattice.{uF, uV} F) (b : Basis.{uF, uV} F) :
    contragredientLatticeEquiv F x (contragredientBasisEquiv F b) = x b :=
  dualLatticeEquiv_coefficient F GeneralLinear.supercuspidalContragredient x b

@[simp]
theorem contragredientLatticeEquiv_symm :
    (contragredientLatticeEquiv.{uF, uV} F).symm = contragredientLatticeEquiv F :=
  dualLatticeEquiv_symm F GeneralLinear.supercuspidalContragredient

@[simp]
theorem contragredientLatticeEquiv_apply_apply (x : Lattice.{uF, uV} F) :
    contragredientLatticeEquiv F (contragredientLatticeEquiv F x) = x :=
  dualLatticeEquiv_apply_apply F GeneralLinear.supercuspidalContragredient x

@[simp]
theorem contragredientLatticeEquiv_trans_self :
    (contragredientLatticeEquiv.{uF, uV} F).trans (contragredientLatticeEquiv F) =
      LinearEquiv.refl ℤ (Lattice.{uF, uV} F) :=
  dualLatticeEquiv_trans_self F GeneralLinear.supercuspidalContragredient

@[simp]
theorem degree_contragredient (x : Lattice.{uF, uV} F) :
    degree F (contragredientLatticeEquiv F x) = degree F x :=
  degree_dualLatticeEquiv F GeneralLinear.supercuspidalContragredient x

/-- Simultaneous contragredients preserve the integral coefficient pairing. -/
theorem pairing_contragredient (x y : Lattice.{uF, uV} F) :
    pairing (contragredientLatticeEquiv F x) (contragredientLatticeEquiv F y) =
      pairing x y :=
  pairing_dualLatticeEquiv F GeneralLinear.supercuspidalContragredient x y

theorem effective_contragredient_iff (x : Lattice.{uF, uV} F) :
    contragredientLatticeEquiv F x ∈ effective ↔ x ∈ effective :=
  effective_dualLatticeEquiv_iff F GeneralLinear.supercuspidalContragredient x

theorem contragredientBasisEquiv_realPowerTwist (s : ℝ) (b : Basis.{uF, uV} F) :
    contragredientBasisEquiv F (realPowerTwistBasisEquiv F s b) =
      realPowerTwistBasisEquiv F (-s) (contragredientBasisEquiv F b) :=
  dualBasisEquiv_realPowerTwist F GeneralLinear.supercuspidalContragredient s b

theorem contragredientLatticeEquiv_realPowerTwist
    (s : ℝ) (x : Lattice.{uF, uV} F) :
    contragredientLatticeEquiv F (realPowerTwistLatticeEquiv F s x) =
      realPowerTwistLatticeEquiv F (-s) (contragredientLatticeEquiv F x) :=
  dualLatticeEquiv_realPowerTwist F GeneralLinear.supercuspidalContragredient s x

/-- Contragredients invert every complex unramified parameter. -/
theorem contragredientBasisEquiv_unramifiedTwist (z : ℂˣ) (b : Basis.{uF, uV} F) :
    contragredientBasisEquiv F (unramifiedTwistBasisEquiv F z b) =
      unramifiedTwistBasisEquiv F z⁻¹ (contragredientBasisEquiv F b) :=
  dualBasisEquiv_unramifiedTwist F GeneralLinear.supercuspidalContragredient z b

theorem contragredientLatticeEquiv_unramifiedTwist
    (z : ℂˣ) (x : Lattice.{uF, uV} F) :
    contragredientLatticeEquiv F (unramifiedTwistLatticeEquiv F z x) =
      unramifiedTwistLatticeEquiv F z⁻¹ (contragredientLatticeEquiv F x) :=
  dualLatticeEquiv_unramifiedTwist F GeneralLinear.supercuspidalContragredient z x

/-- The genuine unitary subset is preserved and reflected by the smooth dual. -/
theorem isUnitaryClass_contragredientBasisEquiv_iff (b : Basis.{uF, uV} F) :
    letI := F.canonicalTopologicalData.topology
    Supercuspidal.IsUnitaryClass F.Carrier (contragredientBasisEquiv F b) ↔
      Supercuspidal.IsUnitaryClass F.Carrier b :=
  isUnitaryClass_dualBasisEquiv_iff F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) b

/-- Restrict the actual smooth dual to genuine unitary supercuspidal classes. -/
abbrev unitaryContragredientBasisEquiv :
    UnitaryBasis.{uF, uV} F ≃ UnitaryBasis.{uF, uV} F :=
  unitaryDualBasisEquiv F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)

@[simp]
theorem unitaryContragredientBasisEquiv_val (b : UnitaryBasis.{uF, uV} F) :
    (unitaryContragredientBasisEquiv F b).val =
      contragredientBasisEquiv F b.val := rfl

@[simp]
theorem unitaryContragredientBasisEquiv_rank (b : UnitaryBasis.{uF, uV} F) :
    (unitaryContragredientBasisEquiv F b).val.1 = b.val.1 := rfl

/-- On a unitary supercuspidal representative this is its actual smooth dual. -/
@[simp]
theorem unitaryContragredientBasisEquiv_unitaryBasisClass (n : ℕ+) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    ∀ (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (n : ℕ)))
      (hA : Langlands.IsUnitarizable A.obj.representation),
      unitaryContragredientBasisEquiv F (Supercuspidal.unitaryBasisClass n A hA) =
        Supercuspidal.unitaryBasisClass n
          (GeneralLinear.SupercuspidalRep.contragredient
            (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n)
            (F.canonicalTopologicalData.supercuspidalContragredientClosed
              GeneralLinear.supercuspidalContragredient n) A)
          (F.canonicalTopologicalData.isUnitarizable_smoothContragredient
            (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)
            n n.pos A.obj A.property.2.1 hA) :=
  unitaryDualBasisEquiv_unitaryBasisClass F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) n

@[simp]
theorem unitaryContragredientBasisEquiv_symm :
    (unitaryContragredientBasisEquiv.{uF, uV} F).symm =
      unitaryContragredientBasisEquiv F :=
  unitaryDualBasisEquiv_symm F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)

@[simp]
theorem unitaryContragredientBasisEquiv_apply_apply (b : UnitaryBasis.{uF, uV} F) :
    unitaryContragredientBasisEquiv F (unitaryContragredientBasisEquiv F b) = b :=
  unitaryDualBasisEquiv_apply_apply F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) b

@[simp]
theorem unitaryContragredientBasisEquiv_trans_self :
    (unitaryContragredientBasisEquiv.{uF, uV} F).trans (unitaryContragredientBasisEquiv F) =
      Equiv.refl (UnitaryBasis.{uF, uV} F) :=
  unitaryDualBasisEquiv_trans_self F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)

/-- Integral smooth duality on the genuine unitary supercuspidal basis. -/
abbrev unitaryContragredientLatticeEquiv :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  unitaryDualLatticeEquiv F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)

@[simp]
theorem unitaryContragredientLatticeEquiv_single (b : UnitaryBasis.{uF, uV} F) (m : ℤ) :
    unitaryContragredientLatticeEquiv F (Finsupp.single b m) =
      Finsupp.single (unitaryContragredientBasisEquiv F b) m :=
  unitaryDualLatticeEquiv_single F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) b m

@[simp]
theorem unitaryContragredientLatticeEquiv_generator (b : UnitaryBasis.{uF, uV} F) :
    unitaryContragredientLatticeEquiv F (generator b) =
      generator (unitaryContragredientBasisEquiv F b) :=
  unitaryDualLatticeEquiv_generator F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) b

@[simp]
theorem unitaryContragredientLatticeEquiv_coefficient
    (x : UnitaryLattice.{uF, uV} F) (b : UnitaryBasis.{uF, uV} F) :
    unitaryContragredientLatticeEquiv F x (unitaryContragredientBasisEquiv F b) = x b :=
  unitaryDualLatticeEquiv_coefficient F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) x b

@[simp]
theorem unitaryContragredientLatticeEquiv_symm :
    (unitaryContragredientLatticeEquiv.{uF, uV} F).symm =
      unitaryContragredientLatticeEquiv F :=
  unitaryDualLatticeEquiv_symm F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)

@[simp]
theorem unitaryContragredientLatticeEquiv_apply_apply (x : UnitaryLattice.{uF, uV} F) :
    unitaryContragredientLatticeEquiv F (unitaryContragredientLatticeEquiv F x) = x :=
  unitaryDualLatticeEquiv_apply_apply F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) x

@[simp]
theorem unitaryContragredientLatticeEquiv_trans_self :
    (unitaryContragredientLatticeEquiv.{uF, uV} F).trans
        (unitaryContragredientLatticeEquiv F) =
      LinearEquiv.refl ℤ (UnitaryLattice.{uF, uV} F) :=
  unitaryDualLatticeEquiv_trans_self F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData)

@[simp]
theorem includeUnitary_contragredient (x : UnitaryLattice.{uF, uV} F) :
    includeUnitary F (unitaryContragredientLatticeEquiv F x) =
      contragredientLatticeEquiv F (includeUnitary F x) :=
  includeUnitary_dual F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) x

@[simp]
theorem unitaryDegree_contragredient (x : UnitaryLattice.{uF, uV} F) :
    unitaryDegree F (unitaryContragredientLatticeEquiv F x) = unitaryDegree F x :=
  unitaryDegree_dual F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) x

theorem unitaryPairing_contragredient (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairing F (unitaryContragredientLatticeEquiv F x)
      (unitaryContragredientLatticeEquiv F y) = unitaryPairing F x y :=
  unitaryPairing_dual F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) x y

theorem effective_unitaryContragredient_iff (x : UnitaryLattice.{uF, uV} F) :
    unitaryContragredientLatticeEquiv F x ∈ effective ↔ x ∈ effective :=
  effective_unitaryDual_iff F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) x

/-- Norm-one unramified twists stay in the unitary basis and invert under duality. -/
theorem unitaryContragredientBasisEquiv_unramifiedTwist
    (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) (b : UnitaryBasis.{uF, uV} F) :
    unitaryContragredientBasisEquiv F (unitaryUnramifiedTwistBasisEquiv F z hz b) =
      unitaryUnramifiedTwistBasisEquiv F z⁻¹ (by simp [hz])
        (unitaryContragredientBasisEquiv F b) :=
  unitaryDualBasisEquiv_unramifiedTwist F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) z hz b

theorem unitaryContragredientLatticeEquiv_unramifiedTwist
    (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) (x : UnitaryLattice.{uF, uV} F) :
    unitaryContragredientLatticeEquiv F (unitaryUnramifiedTwistLatticeEquiv F z hz x) =
      unitaryUnramifiedTwistLatticeEquiv F z⁻¹ (by simp [hz])
        (unitaryContragredientLatticeEquiv F x) :=
  unitaryDualLatticeEquiv_unramifiedTwist F GeneralLinear.supercuspidalContragredient
    (Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData) z hz x

end Langlands.VirtualRepresentation.PadicSupercuspidal
