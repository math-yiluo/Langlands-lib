import Langlands.Global.Arithmetic.AuxiliaryGeneralPositionReductionStatement
import Langlands.Global.Arithmetic.UnitNormWeilStabilizerTransportProof
import Langlands.Global.Arithmetic.GeneralPositionOfExactStabilizerProof
import Langlands.HarmonicAnalysis.CanonicalConductorDepthProof
import Langlands.Weil.Local.ExtensionResidue

noncomputable section

universe u

namespace Langlands.Global

open LocalFactor.CommonClosure GeneralPosition Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private theorem restrictAlgEquiv_continuous
    (E M : Extension F) (h : E.field ≤ M.field) :
    letI := (fieldData F E).topology
    letI := (M.asPadicField (p := p)).canonicalNormedField
    Continuous (IntermediateField.restrictAlgEquiv h) := by
  let := (fieldData F E).topology
  let := (M.asPadicField (p := p)).canonicalNormedField
  let := (E.asPadicField (p := p)).algebra
  let := (M.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier E.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) F.Carrier M.field := IsScalarTower.of_algebraMap_eq' rfl
  let f : E.field →ₐ[Padic p] M.field :=
    (IntermediateField.inclusion h).restrictScalars (Padic p)
  have hc : Continuous f := by
    change @Continuous E.field M.field (fieldData F E).topology _ f
    rw [(fieldData F E).topology_eq_canonicalNormTopology]
    let := (E.asPadicField (p := p)).canonicalNormedField
    exact (extension_isometry (E.asPadicField (p := p))
      (M.asPadicField (p := p)) f).continuous
  exact hc.subtype_mk _

private theorem restrictAlgEquiv_norm
    (E M : Extension F) (h : E.field ≤ M.field) (x : E.field) :
    (M.asPadicField (p := p)).canonicalNorm
        (IntermediateField.restrictAlgEquiv h x : M.field) =
      (E.asPadicField (p := p)).canonicalNorm x := by
  let := (E.asPadicField (p := p)).algebra
  let := (M.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier E.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) F.Carrier M.field := IsScalarTower.of_algebraMap_eq' rfl
  exact canonicalNorm_map (E.asPadicField (p := p)) (M.asPadicField (p := p))
    ((IntermediateField.inclusion h).restrictScalars (Padic p)) x

set_option maxHeartbeats 1000000 in
private theorem exactStabilizer_of_auxiliary
    (haux : AuxiliaryCharacterStatement.{u, u})
    (htransport : UnitNormWeilStabilizerTransportStatement.{u}) :
    ExactStabilizerCharacterStatement.{u} := by
  intro p hp F E e he
  let := (fieldData F E).topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let M := galoisClosure F E
  let h := le_galoisClosure F E
  let L := IntermediateField.restrict h
  let a := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
  let := (M.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier M.field := IsScalarTower.of_algebraMap_eq' rfl
  let := (M.asPadicField (p := p)).canonicalNormedField
  have : IsGalois F.Carrier M.field := by
    change IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier E.field (AlgebraicClosure F.Carrier))
    infer_instance
  let P : FieldCharacter F E → Prop := fun χ =>
    (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) ∧
      HasExactWeilStabilizer F E (weilCharacter F e E χ)
  have hdepth (s : ℕ) : ∃ χ : FieldCharacter F E, P χ ∧
      ∃ x : E.fieldˣ,
        (E.asPadicField (p := p)).canonicalNorm ((x : E.field) - 1) <
          (p : ℝ) ^ (-(s : ℤ)) ∧ χ x ≠ 1 := by
    obtain ⟨χL, horder, ⟨xL, hxL, hnL⟩, hstab⟩ :=
      haux p F (M.asPadicField (p := p)) L s
    let c : E.fieldˣ →ₜ* Lˣ :=
      ⟨a.toMonoidHom, (restrictAlgEquiv_continuous F E M h).units_map _⟩
    let χ : FieldCharacter F E := χL.comp c
    have horder' : ∃ n : ℕ, 0 < n ∧ χ ^ n = 1 := by
      obtain ⟨n, hn, hχn⟩ := horder
      refine ⟨n, hn, ?_⟩
      apply DFunLike.ext
      intro x
      rw [ContinuousMonoidHom.pow_apply]
      change χL (a x) ^ n = 1
      simpa using DFunLike.congr_fun hχn (a x)
    have hpull : χ.toMonoidHom.comp a.symm.toMonoidHom = χL.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change χL (a (a.symm x)) = χL x
      rw [a.apply_symm_apply]
    have hunit : HasExactUnitNormStabilizer L
        (χ.toMonoidHom.comp a.symm.toMonoidHom) := by
      rw [hpull]
      exact hstab
    have hweil := htransport p F E e he χ hunit
    let x := a.symm xL
    have hx : (E.asPadicField (p := p)).canonicalNorm ((x : E.field) - 1) <
        (p : ℝ) ^ (-(s : ℤ)) := by
      rw [← restrictAlgEquiv_norm F E M h]
      have hv : (IntermediateField.restrictAlgEquiv h) (x : E.field) = (xL : L) := by
        exact congrArg (fun z : Lˣ => (z : L)) (a.apply_symm_apply xL)
      rw [map_sub, map_one, hv]
      change (M.asPadicField (p := p)).canonicalNorm (((xL : L) : M.field) - 1) <
        (p : ℝ) ^ (-(s : ℤ))
      exact hxL
    have hn : χ x ≠ 1 := by
      change χL (a (a.symm xL)) ≠ 1
      rw [a.apply_symm_apply]
      exact hnL
    exact ⟨χ, ⟨horder', hweil⟩, x, hx, hn⟩
  have hcond := (HarmonicAnalysis.canonicalConductorDepth.2 p
    (E.asPadicField (p := p)) (fieldData F E) P).mp hdepth
  intro r
  obtain ⟨χ, ⟨horder, hweil⟩, hr⟩ := hcond r
  exact ⟨χ, horder, hr, hweil⟩

/-- The auxiliary-character existence input implies the full original
Harris general-position conjunction, with no other existence premise. -/
theorem auxiliaryGeneralPositionReduction :
    AuxiliaryGeneralPositionReductionStatement.{u} := by
  intro haux
  have hexact := exactStabilizer_of_auxiliary haux unitNormWeilStabilizerTransport
  refine ⟨generalPositionOfExactStabilizer, hexact, ?_⟩
  intro p hp F E e he r
  obtain ⟨χ, horder, hr, hstab⟩ := hexact p F E e he r
  exact ⟨χ, horder, hr, generalPositionOfExactStabilizer p F E
    (weilCharacter F e E χ) hstab⟩

end Langlands.Global
