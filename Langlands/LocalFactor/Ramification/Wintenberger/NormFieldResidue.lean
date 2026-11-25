import Langlands.LocalFactor.Ramification.Wintenberger.NormField
import Langlands.LocalFactor.Ramification.Wintenberger.Degree
import FontaineWintenberger.FieldOfNorms.Estimates.Transfer
import FontaineWintenberger.APF.Tower.AlgebraicResidue

/-!
# Residue actions under the field-of-norms correspondence

For an automorphism `a` of `Ω` over `L`, the action of `a` on the residue field of `Ω` and the
action of the corresponding automorphism of the relative field of norms on its residue field are
the same power of the Frobenius, whenever the first is an integral power: the residue fields of
the finite norm fields `X_K(N)` are those of the finite extensions `N`, compatibly with the
automorphisms (Wintenberger, Théorème 2.1.3 (ii) and its functoriality).
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe uK uL uΩ uX

section Stages

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosure L Ω]

/-- Every element of the relative field of norms lies in the norm field of a finite Galois
stage. -/
theorem exists_mem_stageImage (x : FontaineWintenberger.RelFieldOfNorms K L Ω) :
    ∃ N : FiniteGaloisIntermediateField L Ω, x ∈ stageImage K L Ω N := by
  obtain ⟨Q, y, rfl⟩ := FontaineWintenberger.RelFieldOfNorms.exists_stage K L Ω x
  have : IsGalois L Ω := inferInstance
  let N : FiniteGaloisIntermediateField L Ω := { IntermediateField.normalClosure L Q.val Ω with }
  have hQN : Q ≤ galoisStage L Ω N := IntermediateField.le_normalClosure Q.val
  refine ⟨N, FontaineWintenberger.RelFieldOfNorms.transition K L Ω Q _ hQN y, ?_⟩
  exact FontaineWintenberger.RelFieldOfNorms.of_transition K L Ω Q _ hQN y

end Stages

section FSide

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosure L Ω]
  [Algebra.IsSeparable K Ω]

/-- The integers of `K` act on a stage through `K`, as in the FontaineWintenberger library. -/
@[instance_reducible]
def stageIntegersAlgebra (N : IntermediateField L Ω) :
    Algebra (NormedField.valuation (K := K)).valuationSubring N :=
  Algebra.ofSubsemiring (NormedField.valuation (K := K)).valuationSubring

attribute [local instance high] stageIntegersAlgebra

/-- The integral closure of the integers of `K` in an algebraic extension is a local ring. -/
theorem integralClosure_isLocalRing' (E : Type*) [Field E] [Algebra K E] [Algebra.IsAlgebraic K E] :
    IsLocalRing (integralClosure (NormedField.valuation (K := K)).valuationSubring E) :=
  @ValuationRing.isLocalRing _ _ inferInstance
    (FontaineWintenberger.integralClosure_valuationRing K E).toPreValuationRing

attribute [local instance] integralClosure_isLocalRing'

omit [FontaineWintenberger.IsAPF K L] [Fact (¬ Module.Finite K L)] in
/-- A Frobenius-power residue action of `a` on `Ω` restricts to every finite Galois stage. -/
theorem algebraicResidueAut_stage_isFrobPow (a : Ω ≃ₐ[L] Ω) {q : ℕ} {M : ℤ}
    (h : IsFrobPow (FontaineWintenberger.algebraicResidueAut K Ω (a.restrictScalars K)) q M)
    (N : FiniteGaloisIntermediateField L Ω) :
    IsFrobPow (FontaineWintenberger.algebraicResidueAut K (galoisStage L Ω N).val
      ((a.restrictNormal (galoisStage L Ω N).val).restrictScalars K)) q M := by
  intro z
  let i : (galoisStage L Ω N).val →ₐ[K] Ω := ((galoisStage L Ω N).val.val).restrictScalars K
  let j := FontaineWintenberger.integralClosureResidueInclusion K i
  refine FrobPowAt.of_map j.toRingHom j.toRingHom.injective ?_ (h (j z))
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, j,
    FontaineWintenberger.algebraicResidueAut_residue,
    FontaineWintenberger.integralClosureResidueInclusion_residue]
  congr 1
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes a (galoisStage L Ω N).val (y : _)

end FSide

section USide

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosure K Ω]
  [IsSepClosure L Ω]

omit [IsSepClosure K Ω] in
/-- On the norm field of a finite Galois stage, the automorphism of the relative field of norms
attached to `τ` is the norm-field automorphism of `τ|N`. -/
theorem autEquiv_of_galoisStage (τ : Ω ≃ₐ[L] Ω) (N : FiniteGaloisIntermediateField L Ω)
    (x : FontaineWintenberger.FieldOfNorms K (galoisStage L Ω N).val) :
    FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω τ
        (FontaineWintenberger.RelFieldOfNorms.of K L Ω (galoisStage L Ω N) x) =
      FontaineWintenberger.RelFieldOfNorms.of K L Ω (galoisStage L Ω N)
        (FontaineWintenberger.FieldOfNorms.autEquiv K L (galoisStage L Ω N).val
          (τ.restrictNormal (galoisStage L Ω N).val) x) := by
  rw [FontaineWintenberger.RelFieldOfNorms.autEquiv_of,
    FontaineWintenberger.FieldOfNorms.autEquiv_apply, FontaineWintenberger.RelFieldOfNorms.stageMap_apply]
  apply FontaineWintenberger.RelFieldOfNorms.of_transport_congr K L Ω
  · apply Subtype.ext
    exact (IntermediateField.normal_iff_forall_map_eq'.mp inferInstance τ)
  · intro a
    exact (AlgEquiv.restrictNormal_commutes τ (galoisStage L Ω N).val a).symm

end USide

section Main

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosure K Ω]
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X']
  [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))
  (hval : ∀ x y : X', ValuativeRel.vle x y ↔
    FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ x) ≤
      FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ y))

attribute [local instance high] stageIntegersAlgebra
attribute [local instance] integralClosure_isLocalRing'

local instance normFieldResidueNormedField : NontriviallyNormedField X' :=
  LocalGalois.localNormedField X'
local instance normFieldResidueUltrametric : IsUltrametricDist X' :=
  LocalGalois.localNormedField_ultrametric X'
local instance normFieldResidueComplete : CompleteSpace X' :=
  LocalGalois.localNormedField_complete X'
local instance normFieldResidueLocalField : FontaineWintenberger.IsPerfectResidueLocalField X' :=
  localField_isPerfectResidueLocalField X'

/-- The copy's spectral integers and the Library's spectral integers of a stage. -/
def stageSpectralEquiv (N : FiniteGaloisIntermediateField L Ω) :
    FontaineWintenberger.spectralIntegerRing X' (stageGalois K L Ω X' hbij N) ≃+*
      LocalGalois.extensionIntegers X' (stageGalois K L Ω X' hbij N) :=
  RingEquiv.subringCongr (by ext; rfl)

include hval in
/-- **Residue actions correspond.** If `a` acts on the residue field of `Ω` as an integral power
of the `q`-power map, the corresponding automorphism of the relative field of norms acts on the
residue field of its integers over `X'` as the same power. -/
theorem relFieldOfNorms_residueHom_isFrobPow (a : Ω ≃ₐ[L] Ω) {q : ℕ} {M : ℤ}
    (h : IsFrobPow (FontaineWintenberger.algebraicResidueAut K Ω (a.restrictScalars K)) q M) :
    haveI := relFieldOfNorms_isSepClosure K L Ω X' hbij
    IsFrobPow (⇑(LocalGalois.residueHom X' (FontaineWintenberger.RelFieldOfNorms K L Ω)
      ((FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω a).restrictScalars X'))) q M := by
  have := relFieldOfNorms_isSepClosure K L Ω X' hbij
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨N, hxN⟩ := exists_mem_stageImage K L Ω (x : FontaineWintenberger.RelFieldOfNorms K L Ω)
  let E := (stageGalois K L Ω X' hbij N).toIntermediateField
  have hxE : (x : FontaineWintenberger.RelFieldOfNorms K L Ω) ∈ E := hxN
  let xE : LocalGalois.extensionIntegers X' E := ⟨⟨x, hxE⟩, by
    change spectralNorm X' E ⟨x, hxE⟩ ≤ 1
    rw [spectralNorm.eq_of_tower (L := FontaineWintenberger.RelFieldOfNorms K L Ω)]
    exact x.2⟩
  let w := (stageIntegerEquiv K L Ω X' hbij hval N).symm
    ((stageSpectralEquiv K L Ω X' hbij N).symm xE)
  let σN := (a.restrictNormal (galoisStage L Ω N).val).restrictScalars K
  let r := FontaineWintenberger.FieldOfNorms.residueEquiv K (galoisStage L Ω N).val
  let z' := r.symm (IsLocalRing.residue _ w)
  have h1 := algebraicResidueAut_stage_isFrobPow K L Ω a h N z'
  have h2 := h1.map r.toRingHom
    (FontaineWintenberger.FieldOfNorms.residueAut_residueEquiv K _ σN z').symm
  rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h2
  let j3 : IsLocalRing.ResidueField
      (FontaineWintenberger.FieldOfNorms.fieldValuation K (galoisStage L Ω N).val).valuationSubring →+*
      IsLocalRing.ResidueField (LocalGalois.extensionIntegers X'
        (FontaineWintenberger.RelFieldOfNorms K L Ω)) :=
    (LocalGalois.residueInclusion X' _ E).toRingHom.comp
      ((IsLocalRing.ResidueField.mapEquiv (stageSpectralEquiv K L Ω X' hbij N)).toRingHom.comp
        (IsLocalRing.ResidueField.mapEquiv (stageIntegerEquiv K L Ω X' hbij hval N)).toRingHom)
  have hj : ∀ v, j3 (IsLocalRing.residue _ v) = IsLocalRing.residue _
      (LocalGalois.integerInclusion X' _ E ((stageSpectralEquiv K L Ω X' hbij N)
        (stageIntegerEquiv K L Ω X' hbij hval N v))) := fun v => rfl
  have hcoe : ∀ v, ((LocalGalois.integerInclusion X' _ E ((stageSpectralEquiv K L Ω X' hbij N)
      (stageIntegerEquiv K L Ω X' hbij hval N v)) : FontaineWintenberger.RelFieldOfNorms K L Ω)) =
      FontaineWintenberger.RelFieldOfNorms.of K L Ω (galoisStage L Ω N) v := fun v => rfl
  have h3 := h2.map j3 (τ' := ⇑(LocalGalois.residueHom X' (FontaineWintenberger.RelFieldOfNorms K L Ω)
      ((FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω a).restrictScalars X'))) (by
    rw [FontaineWintenberger.FieldOfNorms.residueAut_residue, hj, hj]
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ (LocalGalois.integerAut X' _ _ _)
    congr 1
    apply Subtype.ext
    rw [hcoe]
    change _ = FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω a
      ((LocalGalois.integerInclusion X' _ E ((stageSpectralEquiv K L Ω X' hbij N)
        (stageIntegerEquiv K L Ω X' hbij hval N w)) : FontaineWintenberger.RelFieldOfNorms K L Ω))
    rw [hcoe, autEquiv_of_galoisStage]
    rfl)
  have hx : j3 (IsLocalRing.residue _ w) = IsLocalRing.residue _ x := by
    rw [hj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rfl
  rw [hx] at h3
  exact h3

include hbij hval in
/-- **Residue degrees correspond.** If `a` acts on the residue field of `Ω` as the `(-n)`-th power
of the `q`-power map, `q` the cardinality of the residue field of `X'`, the automorphism of a
separable closure `Ω'` of `X'` corresponding to `a` (through the relative field of norms and an
isomorphism `e` of separable closures) has residue degree `n`. -/
theorem relFieldOfNorms_localResidueDegree (Ω' : Type*) [Field Ω'] [Algebra X' Ω']
    [Algebra.IsAlgebraic X' Ω'] [IsSepClosed Ω'] (e : FontaineWintenberger.RelFieldOfNorms K L Ω ≃ₐ[X'] Ω')
    (a : Ω ≃ₐ[L] Ω) (n : ℤ) {q : ℕ} (hq : Nat.card (Weil.Local.SepClosed.localResidueField X') = q)
    (h : IsFrobPow (FontaineWintenberger.algebraicResidueAut K Ω (a.restrictScalars K)) q (-n)) :
    Weil.Local.SepClosed.localResidueDegree X' Ω'
        (e.autCongr ((FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω a).restrictScalars X')) =
      Weil.frobenius (Multiplicative.ofAdd n) := by
  subst hq
  have := relFieldOfNorms_isSepClosure K L Ω X' hbij
  have h3 := relFieldOfNorms_residueHom_isFrobPow K L Ω X' hbij hval a h
  exact (localResidueDegree_eq_frobenius_iff X' Ω' _ n).mpr
    (residueHom_autCongr_isFrobPow X' e _ h3)

end Main

end Langlands.Ramification.Wintenberger
