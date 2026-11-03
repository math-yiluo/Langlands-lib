import Langlands.Global.Arithmetic.UnitNormWeilStabilizerTransportStatement
import Mathlib.RingTheory.Norm.Basic

noncomputable section

universe u

namespace Langlands.Global

open LocalFactor.CommonClosure GeneralPosition LocalClassField Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private theorem reciprocityUnits_norm
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (E M : Extension F) (h : E.field ≤ M.field)
    (x : weilSubgroup F M) :
    reciprocityUnits F e E (Subgroup.inclusion (weilSubgroup_antitone F E M h) x) =
      E.unitsNorm M h (reciprocityUnits F e M x) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have hn := he.1.1 E M h
  exact DFunLike.congr_fun hn (abelianizationProjection _ x)

private theorem reciprocityUnits_surjective
    (e : ReciprocityFamily F) (E : Extension F) :
    Function.Surjective (reciprocityUnits F e E) := by
  let := (fieldData F E).topology
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective ((e E).symm z)
  refine ⟨x, ?_⟩
  change e E (QuotientGroup.mk x) = z
  rw [hx]
  exact (e E).apply_symm_apply z

private theorem reciprocityUnits_field_eq
    (e : ReciprocityFamily F) (A B : Extension F) (h : A.field = B.field)
    (x : weilSubgroup F A) (y : weilSubgroup F B)
    (hxy : (x : localWeilGroup F) = (y : localWeilGroup F)) :
    ((reciprocityUnits F e A x : A.field) : AlgebraicClosure F.Carrier) =
      ((reciprocityUnits F e B y : B.field) : AlgebraicClosure F.Carrier) := by
  have hAB : A = B := Subtype.ext h
  subst B
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

private theorem reciprocityUnits_conj_normal
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (M : Extension F) [Normal F.Carrier M.field] [(weilSubgroup F M).Normal]
    (w : localWeilGroup F) (x : weilSubgroup F M) :
    reciprocityUnits F e M ((MulAut.conjNormal w) x) =
      Units.map ((Weil.projection (localResidueDegree F) w).restrictNormal
        M.field).toRingEquiv.toMonoidHom (reciprocityUnits F e M x) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let σ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    Weil.projection (localResidueDegree F) w
  have hM : (M.conj σ).field = M.field :=
    IntermediateField.normal_iff_forall_map_eq'.mp inferInstance σ
  have hc := DFunLike.congr_fun (he.1.2.2.1 w M) (abelianizationProjection _ x)
  have hc' : reciprocityUnits F e (M.conj σ)
      (M.weilConjugation (localResidueDegree F) w x) =
      M.unitsConjugation σ (reciprocityUnits F e M x) := hc
  apply Units.ext
  apply Subtype.ext
  calc
    ((reciprocityUnits F e M ((MulAut.conjNormal w) x) : M.field) :
        AlgebraicClosure F.Carrier) =
      ((reciprocityUnits F e (M.conj σ)
        (M.weilConjugation (localResidueDegree F) w x) : (M.conj σ).field) :
        AlgebraicClosure F.Carrier) :=
      reciprocityUnits_field_eq F e M (M.conj σ) hM.symm _ _ rfl
    _ = σ ((reciprocityUnits F e M x : M.field) : AlgebraicClosure F.Carrier) := by
      rw [hc']
      rfl
    _ = ((Units.map (σ.restrictNormal M.field).toRingEquiv.toMonoidHom
        (reciprocityUnits F e M x) : M.field) : AlgebraicClosure F.Carrier) :=
      (AlgEquiv.restrictNormal_commutes σ M.field _).symm

private theorem unitsNorm_restrict
    (E M : Extension F) (h : E.field ≤ M.field) (z : M.fieldˣ) :
    Units.map (IntermediateField.restrictAlgEquiv h).toRingEquiv.toMonoidHom
        (E.unitsNorm M h z) =
      Units.map (Algebra.norm (IntermediateField.restrict h)) z := by
  let : Algebra E.field M.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field M.field :=
    FiniteDimensional.right F.Carrier E.field M.field
  apply Units.ext
  change (IntermediateField.restrictAlgEquiv h)
      (Algebra.norm E.field (z : M.field)) =
    Algebra.norm (IntermediateField.restrict h) (z : M.field)
  apply Algebra.norm_eq_of_ringEquiv (IntermediateField.restrictAlgEquiv h).toRingEquiv
  ext x
  rfl

private theorem normCharacter_restrict
    (E M : Extension F) (h : E.field ≤ M.field) (χ : E.fieldˣ →* ℂˣ)
    (z : M.fieldˣ) :
    (χ.comp (Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv).symm.toMonoidHom)
      (Units.map (Algebra.norm (IntermediateField.restrict h)) z) =
      χ (E.unitsNorm M h z) := by
  let a := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
  have hn : a (E.unitsNorm M h z) =
      Units.map (Algebra.norm (IntermediateField.restrict h)) z :=
    unitsNorm_restrict F E M h z
  change χ (a.symm (Units.map (Algebra.norm (IntermediateField.restrict h)) z)) = _
  rw [← hn, a.symm_apply_apply]

set_option maxHeartbeats 800000 in
private theorem closureRestriction_inner
    (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ)
    (g : localWeilGroup F) (hg : g ∈ weilSubgroup F E) :
    (closureRestriction F E χ).comp (MulAut.conjNormal g⁻¹).toMonoidHom =
      closureRestriction F E χ := by
  apply MonoidHom.ext
  intro x
  let h := galoisClosure_weilSubgroup_le F E
  let gE : weilSubgroup F E := ⟨g, hg⟩
  have harg : Subgroup.inclusion h ((MulAut.conjNormal g⁻¹) x) =
      gE⁻¹ * Subgroup.inclusion h x * gE := by
    apply Subtype.ext
    change g⁻¹ * (x : localWeilGroup F) * (g⁻¹)⁻¹ = g⁻¹ * (x : localWeilGroup F) * g
    rw [inv_inv]
  change χ (Subgroup.inclusion h ((MulAut.conjNormal g⁻¹) x)) =
    χ (Subgroup.inclusion h x)
  rw [harg, map_mul, map_mul, map_inv]
  calc
    _ = χ (Subgroup.inclusion h x) * ((χ gE)⁻¹ * χ gE) := by ac_rfl
    _ = χ (Subgroup.inclusion h x) := by rw [inv_mul_cancel, mul_one]

private theorem restrictNormal_mem_fixing_iff
    (E M : Extension F) [Normal F.Carrier M.field] (h : E.field ≤ M.field)
    (σ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier) :
    σ.restrictNormal M.field ∈ (IntermediateField.restrict h).fixingSubgroup ↔
      σ ∈ E.field.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ x hx
    let y : E.field := ⟨x, hx⟩
    let yL := IntermediateField.restrictAlgEquiv h y
    have hfix := hσ (yL : M.field) yL.property
    have hc := congrArg (fun t : M.field => (t : AlgebraicClosure F.Carrier)) hfix
    rw [AlgEquiv.restrictNormal_apply] at hc
    exact hc
  · intro hσ x hx
    apply Subtype.ext
    rw [AlgEquiv.restrictNormal_apply]
    exact hσ (x : AlgebraicClosure F.Carrier) ((IntermediateField.mem_restrict h x).mp hx)

set_option maxHeartbeats 1000000 in
/-- Harris's exact unit-norm stabilizer implies his exact Weil stabilizer
through the actual norm and conjugation reciprocity squares. -/
theorem unitNormWeilStabilizerTransport : UnitNormWeilStabilizerTransportStatement.{u} := by
  intro p hp F E e he
  let := (fieldData F E).topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  intro χ
  let M := galoisClosure F E
  let h := le_galoisClosure F E
  let L := IntermediateField.restrict h
  let a := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
  let χL := χ.toMonoidHom.comp a.symm.toMonoidHom
  let := (M.asPadicField (p := p)).canonicalNormedField
  have : IsGalois F.Carrier M.field := by
    change IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier E.field (AlgebraicClosure F.Carrier))
    infer_instance
  change HasExactUnitNormStabilizer L χL →
    HasExactWeilStabilizer F E (weilCharacter F e E χ)
  intro hunit g
  constructor
  · intro hstab
    let σ := (Weil.projection (localResidueDegree F) g⁻¹).restrictNormal M.field
    have hχnorm (x : weilSubgroup F M) :
        closureRestriction F E (weilCharacter F e E χ) x =
          χ (E.unitsNorm M h (reciprocityUnits F e M x)) :=
      congrArg χ (reciprocityUnits_norm F e he E M h x)
    have hall (z : M.fieldˣ) :
        χL (Units.map (Algebra.norm L) (Units.map σ.toRingEquiv.toMonoidHom z)) =
          χL (Units.map (Algebra.norm L) z) := by
      obtain ⟨x, rfl⟩ := reciprocityUnits_surjective F e M z
      rw [normCharacter_restrict F E M h χ.toMonoidHom,
        normCharacter_restrict F E M h χ.toMonoidHom]
      rw [← reciprocityUnits_conj_normal F e he M g⁻¹ x]
      have hx := DFunLike.congr_fun hstab x
      change closureRestriction F E (weilCharacter F e E χ)
          ((MulAut.conjNormal g⁻¹) x) =
        closureRestriction F E (weilCharacter F e E χ) x at hx
      rw [hχnorm, hχnorm] at hx
      exact hx
    have hfix : σ ∈ L.fixingSubgroup := (hunit σ).mp (fun z _ => hall z)
    have hg_inv : g⁻¹ ∈ weilSubgroup F E :=
      (restrictNormal_mem_fixing_iff F E M h
        (Weil.projection (localResidueDegree F) g⁻¹)).mp hfix
    exact (weilSubgroup F E).inv_mem_iff.mp hg_inv
  · intro hg
    exact closureRestriction_inner F E (weilCharacter F e E χ) g hg

end Langlands.Global
