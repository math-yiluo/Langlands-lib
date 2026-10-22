import Langlands.LocalField.CanonicalProof
import Langlands.Weil.Local.ResidueCharacters

open scoped ValuativeRel

namespace Langlands.Weil.Local

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (E : PadicField.{v} p)

/-- Every embedding over the fixed p-adic base preserves its extended norm. -/
theorem canonicalNorm_map (f : F.Carrier →ₐ[Padic p] E.Carrier) (x : F.Carrier) :
    E.canonicalNorm (f x) = F.canonicalNorm x := by
  unfold PadicField.canonicalNorm spectralNorm
  rw [minpoly.algHom_eq f f.injective]

/-- The actual field embedding is an isometry for the canonical norms. -/
theorem extension_isometry (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    letI := F.canonicalNormedField
    letI := E.canonicalNormedField
    Isometry f := by
  let := F.canonicalNormedField
  let := E.canonicalNormedField
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact canonicalNorm_map F E f (x - y)

/-- Restriction of an actual p-adic field embedding to the canonical integer rings. -/
noncomputable def extensionIntegerMap (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    F.canonicalTopologicalData.Integers →+* E.canonicalTopologicalData.Integers := by
  letI := F.canonicalTopologicalData.valuativeRel
  letI := E.canonicalTopologicalData.valuativeRel
  refine (f.toRingHom.comp
    (ValuativeRel.valuation F.Carrier).integer.subtype).codRestrict
      E.canonicalTopologicalData.Integers ?_
  intro x
  change ValuativeRel.valuation E.Carrier (f x.val) ≤ 1
  rw [← (ValuativeRel.valuation E.Carrier).vle_one_iff,
    E.canonicalTopologicalData_vle]
  rw [canonicalNorm_map, show E.canonicalNorm 1 = 1 by
    simpa using E.canonicalNorm_algebraMap (1 : Padic p)]
  have hx := ((ValuativeRel.valuation F.Carrier).vle_one_iff).mpr x.property
  rw [F.canonicalTopologicalData_vle] at hx
  rw [show F.canonicalNorm 1 = 1 by
    simpa using F.canonicalNorm_algebraMap (1 : Padic p)] at hx
  simpa using hx

@[simp] theorem extensionIntegerMap_coe
    (f : F.Carrier →ₐ[Padic p] E.Carrier) (x : F.canonicalTopologicalData.Integers) :
    (extensionIntegerMap F E f x : E.Carrier) = f (x : F.Carrier) := rfl

@[simp] theorem extensionIntegerMap_id :
    extensionIntegerMap F F (AlgHom.id (Padic p) F.Carrier) = RingHom.id _ := by
  ext x
  rfl

theorem extensionIntegerMap_comp (D : PadicField.{w} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier) (g : E.Carrier →ₐ[Padic p] D.Carrier) :
    extensionIntegerMap F D (g.comp f) =
      (extensionIntegerMap E D g).comp (extensionIntegerMap F E f) := by
  ext x
  rfl

instance extensionIntegerMap_isLocalHom (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    IsLocalHom (extensionIntegerMap F E f) := by
  let := F.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.valuativeRel
  constructor
  intro x hx
  by_contra h
  have hlt := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp h
  have hlt' :
      ValuativeRel.valuation E.Carrier
        (extensionIntegerMap F E f x : E.Carrier) < 1 := by
    rw [← (ValuativeRel.valuation E.Carrier).vlt_one_iff]
    rw [← (ValuativeRel.valuation F.Carrier).vlt_one_iff] at hlt
    rw [ValuativeRel.vlt, F.canonicalTopologicalData_vle,
      show F.canonicalNorm 1 = 1 by
        simpa using F.canonicalNorm_algebraMap (1 : Padic p)] at hlt
    rw [ValuativeRel.vlt, E.canonicalTopologicalData_vle,
      show E.canonicalNorm 1 = 1 by
        simpa using E.canonicalNorm_algebraMap (1 : Padic p)]
    simpa only [extensionIntegerMap_coe, canonicalNorm_map] using hlt
  exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt') hx

/-- The induced map of the actual residue fields; no residue map is input data. -/
noncomputable def extensionResidueMap (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    F.canonicalTopologicalData.ResidueField →+* E.canonicalTopologicalData.ResidueField :=
  IsLocalRing.ResidueField.map (extensionIntegerMap F E f)

@[simp] theorem extensionResidueMap_residue
    (f : F.Carrier →ₐ[Padic p] E.Carrier) (x : F.canonicalTopologicalData.Integers) :
    extensionResidueMap F E f (F.canonicalTopologicalData.residue x) =
      E.canonicalTopologicalData.residue (extensionIntegerMap F E f x) := rfl

@[simp] theorem extensionResidueMap_id :
    extensionResidueMap F F (AlgHom.id (Padic p) F.Carrier) = RingHom.id _ := by
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

theorem extensionResidueMap_comp (D : PadicField.{w} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier) (g : E.Carrier →ₐ[Padic p] D.Carrier) :
    extensionResidueMap F D (g.comp f) =
      (extensionResidueMap E D g).comp (extensionResidueMap F E f) := by
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

/-- Explicit scalar structure of the relative residue extension. -/
noncomputable abbrev extensionResidueAlgebra (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    Algebra F.canonicalTopologicalData.ResidueField E.canonicalTopologicalData.ResidueField :=
  (extensionResidueMap F E f).toAlgebra

/-- The relative residue degree of an actual field embedding. -/
noncomputable def extensionResidueDegree (f : F.Carrier →ₐ[Padic p] E.Carrier) : ℕ :=
  letI := extensionResidueAlgebra F E f
  Module.finrank F.canonicalTopologicalData.ResidueField E.canonicalTopologicalData.ResidueField

private theorem canonicalResidue_finite : Finite F.canonicalTopologicalData.ResidueField := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance

theorem extensionResidueDegree_pos (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    0 < extensionResidueDegree F E f := by
  let := extensionResidueAlgebra F E f
  let := canonicalResidue_finite E
  exact Module.finrank_pos

/-- The actual residue cardinalities satisfy the relative degree formula. -/
theorem extensionResidueCardinality (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    E.canonicalTopologicalData.residueCardinality =
      F.canonicalTopologicalData.residueCardinality ^ extensionResidueDegree F E f := by
  let := extensionResidueAlgebra F E f
  let := canonicalResidue_finite F
  let := canonicalResidue_finite E
  let := Fintype.ofFinite F.canonicalTopologicalData.ResidueField
  let := Fintype.ofFinite E.canonicalTopologicalData.ResidueField
  simpa only [Fintype.card_eq_nat_card, PadicField.TopologicalData.residueCardinality,
    extensionResidueDegree] using (Module.card_eq_pow_finrank
    (K := F.canonicalTopologicalData.ResidueField)
    (V := E.canonicalTopologicalData.ResidueField))

@[simp] theorem extensionResidueDegree_id :
    extensionResidueDegree F F (AlgHom.id (Padic p) F.Carrier) = 1 := by
  change @Module.finrank F.canonicalTopologicalData.ResidueField
    F.canonicalTopologicalData.ResidueField _ _
    (extensionResidueMap F F (AlgHom.id (Padic p) F.Carrier)).toAlgebra.toModule = 1
  rw [extensionResidueMap_id]
  exact Module.finrank_self _

theorem extensionResidueDegree_comp (D : PadicField.{w} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier) (g : E.Carrier →ₐ[Padic p] D.Carrier) :
    extensionResidueDegree F D (g.comp f) =
      extensionResidueDegree F E f * extensionResidueDegree E D g := by
  let := extensionResidueAlgebra F E f
  let := extensionResidueAlgebra E D g
  let := extensionResidueAlgebra F D (g.comp f)
  let : IsScalarTower F.canonicalTopologicalData.ResidueField
      E.canonicalTopologicalData.ResidueField D.canonicalTopologicalData.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change extensionResidueMap F D (g.comp f) x =
        extensionResidueMap E D g (extensionResidueMap F E f x)
      rw [extensionResidueMap_comp]
      rfl
  exact (Module.finrank_mul_finrank F.canonicalTopologicalData.ResidueField
    E.canonicalTopologicalData.ResidueField D.canonicalTopologicalData.ResidueField).symm

theorem extensionResidueCardinalityUnit (f : F.Carrier →ₐ[Padic p] E.Carrier) :
    residueCardinalityUnit E.canonicalTopologicalData =
      residueCardinalityUnit F.canonicalTopologicalData ^ extensionResidueDegree F E f := by
  apply Units.ext
  change (E.canonicalTopologicalData.residueCardinality : ℂ) =
    (F.canonicalTopologicalData.residueCardinality : ℂ) ^ extensionResidueDegree F E f
  exact_mod_cast extensionResidueCardinality F E f

end Langlands.Weil.Local
