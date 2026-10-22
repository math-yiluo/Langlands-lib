import Langlands.LocalField.Normalization.Proof
import Langlands.Weil.Local.ExtensionResidue

/-! Relative integer and residue maps for the supplied local-field realizations. -/

namespace Langlands.PadicField.TopologicalData

universe u v w
section Relative

variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable (T : F.TopologicalData) (S : E.TopologicalData)

/-- Integer membership is preserved and reflected by the actual field extension. -/
theorem relative_mem_integers_iff (x : F.Carrier) :
    algebraMap F.Carrier E.Carrier x ∈ S.Integers ↔ x ∈ T.Integers := by
  rw [← S.canonicalNorm_le_one_iff_mem_integers,
    ← T.canonicalNorm_le_one_iff_mem_integers]
  exact congrArg (fun r : ℝ => r ≤ 1)
    (Langlands.Weil.Local.canonicalNorm_map F E
      (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier) x) |>.to_iff

/-- Restriction of the given field algebra map to the supplied integer rings. -/
noncomputable def relativeIntegerMap : T.Integers →+* S.Integers := by
  let := T.valuativeRel
  let := S.valuativeRel
  refine ((algebraMap F.Carrier E.Carrier).comp
    (ValuativeRel.valuation F.Carrier).integer.subtype).codRestrict S.Integers ?_
  intro x
  exact (relative_mem_integers_iff T S x.val).mpr x.property

@[simp] theorem relativeIntegerMap_coe (x : T.Integers) :
    (relativeIntegerMap T S x : E.Carrier) = algebraMap F.Carrier E.Carrier (x : F.Carrier) := rfl

/-- The restricted map reflects units; its residue map is therefore defined. -/
instance relativeIntegerMap_isLocalHom : IsLocalHom (relativeIntegerMap T S) := by
  constructor
  intro x hx
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hmul : algebraMap F.Carrier E.Carrier x.val * y.val = 1 :=
    congrArg Subtype.val hy
  have hinv : algebraMap F.Carrier E.Carrier x.val⁻¹ = y.val := by
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right hmul
  have hm : x.val⁻¹ ∈ T.Integers :=
    (relative_mem_integers_iff T S x.val⁻¹).mp (by rw [hinv]; exact y.property)
  refine isUnit_iff_exists_inv.mpr ⟨⟨x.val⁻¹, hm⟩, Subtype.ext ?_⟩
  change x.val * x.val⁻¹ = 1
  apply (algebraMap F.Carrier E.Carrier).injective
  simpa only [map_mul, hinv, map_one] using hmul

/-- The induced homomorphism on the supplied residue fields. -/
noncomputable def relativeResidueMap : T.ResidueField →+* S.ResidueField :=
  IsLocalRing.ResidueField.map (relativeIntegerMap T S)

@[simp] theorem relativeResidueMap_residue (x : T.Integers) :
    relativeResidueMap T S (T.residue x) = S.residue (relativeIntegerMap T S x) := rfl

/-- Explicit relative integer scalars; install locally when needed. -/
noncomputable abbrev relativeIntegerAlgebra : Algebra T.Integers S.Integers :=
  (relativeIntegerMap T S).toAlgebra

/-- Explicit relative residue scalars; install locally when needed. -/
noncomputable abbrev relativeResidueAlgebra : Algebra T.ResidueField S.ResidueField :=
  (relativeResidueMap T S).toAlgebra

@[simp] theorem relativeIntegerAlgebra_algebraMap :
    letI := relativeIntegerAlgebra T S
    algebraMap T.Integers S.Integers = relativeIntegerMap T S := rfl

@[simp] theorem relativeResidueAlgebra_algebraMap :
    letI := relativeResidueAlgebra T S
    algebraMap T.ResidueField S.ResidueField = relativeResidueMap T S := rfl

/-- Integer scalars on the extension field, through the actual field embedding. -/
noncomputable abbrev relativeIntegerFieldAlgebra : Algebra T.Integers E.Carrier :=
  Algebra.compHom E.Carrier (algebraMap T.Integers F.Carrier)

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
/-- Compatibility with the actual field extension. -/
theorem relativeIntegerFieldTower :
    letI := relativeIntegerFieldAlgebra (E := E) T
    IsScalarTower T.Integers F.Carrier E.Carrier := by
  let := relativeIntegerFieldAlgebra (E := E) T
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Compatibility with the inclusion of the target integer ring into its field. -/
theorem relativeIntegerTower :
    letI := relativeIntegerAlgebra T S
    letI := relativeIntegerFieldAlgebra (E := E) T
    IsScalarTower T.Integers S.Integers E.Carrier := by
  let := relativeIntegerAlgebra T S
  let := relativeIntegerFieldAlgebra (E := E) T
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The relative map commutes with the published base integer maps. -/
theorem relativeIntegerMap_baseIntegerMap :
    (relativeIntegerMap T S).comp T.baseIntegerMap = S.baseIntegerMap := by
  ext x
  exact (IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier x.val).symm

/-- Compatibility over the actual valuation integer ring of `Padic p`. -/
theorem relativeBaseIntegerTower :
    letI := T.integerAlgebra
    letI := S.integerAlgebra
    letI := relativeIntegerAlgebra T S
    IsScalarTower (ValuativeRel.valuation (Padic p)).integer T.Integers S.Integers := by
  let := T.integerAlgebra
  let := S.integerAlgebra
  let := relativeIntegerAlgebra T S
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (DFunLike.congr_fun (relativeIntegerMap_baseIntegerMap T S) x).symm

/-- Compatibility between the relative integer and relative residue scalars. -/
theorem relativeResidueTower :
    letI := relativeIntegerAlgebra T S
    letI := relativeResidueAlgebra T S
    IsScalarTower T.Integers T.ResidueField S.ResidueField := by
  let := relativeIntegerAlgebra T S
  let := relativeResidueAlgebra T S
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The relative residue map commutes with the published prime-field maps. -/
theorem relativeResidueMap_residueScalarMap :
    (relativeResidueMap T S).comp T.residueScalarMap = S.residueScalarMap := by
  exact Subsingleton.elim _ _

/-- Compatibility with the published residue scalar structures over `ZMod p`. -/
theorem relativeBaseResidueTower :
    letI := T.residueAlgebra
    letI := S.residueAlgebra
    letI := relativeResidueAlgebra T S
    IsScalarTower (ZMod p) T.ResidueField S.ResidueField := by
  let := T.residueAlgebra
  let := S.residueAlgebra
  let := relativeResidueAlgebra T S
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (DFunLike.congr_fun (relativeResidueMap_residueScalarMap T S) x).symm

/-- The canonical specialization is the existing integer map of this embedding. -/
theorem relativeIntegerMap_canonical :
    relativeIntegerMap F.canonicalTopologicalData E.canonicalTopologicalData =
      Langlands.Weil.Local.extensionIntegerMap F E
        (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier) := by
  ext x
  rfl

/-- The canonical specialization is the existing residue map of this embedding. -/
theorem relativeResidueMap_canonical :
    relativeResidueMap F.canonicalTopologicalData E.canonicalTopologicalData =
      Langlands.Weil.Local.extensionResidueMap F E
        (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier) := by
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

variable {D : PadicField.{w} p}
variable [Algebra E.Carrier D.Carrier] [Algebra F.Carrier D.Carrier]
variable [IsScalarTower (Padic p) E.Carrier D.Carrier]
variable [IsScalarTower (Padic p) F.Carrier D.Carrier]
variable [IsScalarTower F.Carrier E.Carrier D.Carrier]
variable (U : D.TopologicalData)

/-- Restriction commutes with composition of the compatible field embeddings. -/
theorem relativeIntegerMap_comp :
    relativeIntegerMap T U = (relativeIntegerMap S U).comp (relativeIntegerMap T S) := by
  ext x
  exact IsScalarTower.algebraMap_apply F.Carrier E.Carrier D.Carrier x.val

/-- Reduction commutes with composition of the compatible field embeddings. -/
theorem relativeResidueMap_comp :
    relativeResidueMap T U = (relativeResidueMap S U).comp (relativeResidueMap T S) := by
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  change U.residue (relativeIntegerMap T U y) =
    U.residue (relativeIntegerMap S U (relativeIntegerMap T S y))
  rw [relativeIntegerMap_comp T S U]
  rfl

/-- Explicit compatibility of the three relative integer scalar structures. -/
theorem relativeIntegerAlgebraTower :
    letI := relativeIntegerAlgebra T S
    letI := relativeIntegerAlgebra S U
    letI := relativeIntegerAlgebra T U
    IsScalarTower T.Integers S.Integers U.Integers := by
  let := relativeIntegerAlgebra T S
  let := relativeIntegerAlgebra S U
  let := relativeIntegerAlgebra T U
  exact IsScalarTower.of_algebraMap_eq fun x =>
    DFunLike.congr_fun (relativeIntegerMap_comp T S U) x

/-- Explicit compatibility of the three relative residue scalar structures. -/
theorem relativeResidueAlgebraTower :
    letI := relativeResidueAlgebra T S
    letI := relativeResidueAlgebra S U
    letI := relativeResidueAlgebra T U
    IsScalarTower T.ResidueField S.ResidueField U.ResidueField := by
  let := relativeResidueAlgebra T S
  let := relativeResidueAlgebra S U
  let := relativeResidueAlgebra T U
  exact IsScalarTower.of_algebraMap_eq fun x =>
    DFunLike.congr_fun (relativeResidueMap_comp T S U) x

end Relative

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}

@[simp] theorem relativeIntegerMap_id (T : F.TopologicalData) :
    relativeIntegerMap T T = RingHom.id T.Integers := by
  ext x
  rfl

@[simp] theorem relativeResidueMap_id (T : F.TopologicalData) :
    relativeResidueMap T T = RingHom.id T.ResidueField := by
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

/-- Equality with the existing canonical map after choosing the scalars of `f`. -/
theorem relativeIntegerMap_canonical_of_algHom (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    letI := f.toRingHom.toAlgebra
    relativeIntegerMap F.canonicalTopologicalData E.canonicalTopologicalData =
      Langlands.Weil.Local.extensionIntegerMap F E f := by
  let := f.toRingHom.toAlgebra
  ext x
  rfl

/-- Equality with the existing canonical residue map after choosing the scalars of `f`. -/
theorem relativeResidueMap_canonical_of_algHom (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    letI := f.toRingHom.toAlgebra
    relativeResidueMap F.canonicalTopologicalData E.canonicalTopologicalData =
      Langlands.Weil.Local.extensionResidueMap F E f := by
  let := f.toRingHom.toAlgebra
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

end Langlands.PadicField.TopologicalData
