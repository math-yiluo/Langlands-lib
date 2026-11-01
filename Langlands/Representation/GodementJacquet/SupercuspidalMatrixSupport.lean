import Langlands.Representation.GodementJacquet.CentralCoefficientSupport
import Langlands.Representation.GodementJacquet.CentralCompactSupport
import Langlands.Representation.GodementJacquet.SupercuspidalCoefficientTests
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof

/-! # Compact scalar support of actual supercuspidal coefficient spans -/

noncomputable section

namespace Langlands.GodementJacquet

universe uG uF uV

section Coefficients

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Functions with the prescribed scalar covariance under the full center. -/
def centralCovariantFunctions (χ : Subgroup.center G →* ℂˣ) :
    Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (z : Subgroup.center G) (g : G), f (z * g) = (χ z : ℂ) * f g}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg z x
    change f (z * x) + g (z * x) = _
    rw [hf, hg]
    exact (mul_add _ _ _).symm
  smul_mem' := by
    intro c f hf z x
    change c * f (z * x) = (χ z : ℂ) * (c * f x)
    rw [hf]
    ring

omit [IsTopologicalGroup G] in
/-- Central scalar action on the actual representation extends to the
entire bi-smooth coefficient span. -/
theorem biSmoothMatrixCoefficients_le_centralCovariantFunctions
    (ρ : Representation ℂ G V) (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ (z : Subgroup.center G) (v : V), ρ (z : G) v = (χ z : ℂ) • v) :
    biSmoothMatrixCoefficients ρ ≤ centralCovariantFunctions χ := by
  apply Submodule.span_le.mpr
  rintro f ⟨ℓ, v, rfl⟩ z g
  change smoothDualPairing ρ ℓ (ρ ((z : G) * g) v.val) = _
  rw [map_mul, Module.End.mul_apply, hχ, map_smul]
  rfl

/-- Every function in the actual coefficient span is continuous. -/
theorem continuous_of_mem_biSmoothMatrixCoefficients
    (ρ : Representation ℂ G V) (f : G → ℂ) (hf : f ∈ biSmoothMatrixCoefficients ρ) :
    Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ℓ, v, rfl⟩ := hf
    exact (matrixCoefficient_isLocallyConstant ρ _ _ v.property).continuous
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact continuous_const.smul hf

end Coefficients

section PadicSupport

open GeneralLinear CuspidalSupport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

/-- The GL determinant-unit subgroup has finite index after adjoining the
center, by the published one-block product-Levi result. -/
theorem determinantNorm_ker_sup_center_finiteIndex :
    ((T.determinantNorm (n + 1)).ker ⊔
      Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier)).FiniteIndex := by
  let B := LeviAdmissibility.oneBlock (n + 1) (Nat.zero_lt_succ n)
  let : Unique (Fin B.length) := by
    change Unique (Fin 1)
    infer_instance
  let : NeZero B.length := by
    change NeZero 1
    infer_instance
  let e : B.Levi F.Carrier ≃* Langlands.GeneralLinear (n + 1) F.Carrier :=
    MulEquiv.piUnique _
  have hker : (determinantUnitSubgroup T B).map e.toMonoidHom =
      (T.determinantNorm (n + 1)).ker := by
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (mem_determinantUnitSubgroup T B m).mp hm 0
    · intro hg
      refine ⟨fun _ => g, ?_, rfl⟩
      exact (mem_determinantUnitSubgroup T B _).mpr fun _ => hg
  have hmap : (determinantUnitSubgroup T B ⊔
      Subgroup.center (B.Levi F.Carrier)).map e.toMonoidHom =
      (T.determinantNorm (n + 1)).ker ⊔
        Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier) := by
    rw [Subgroup.map_sup, hker]
    congr 1
    exact Subgroup.map_center_eq e
  have := determinantUnit_sup_center_finiteIndex T B
  rw [← hmap]
  exact Subgroup.FiniteIndex.map_of_surjective _ e.surjective

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Irreducible supercuspidality supplies the actual scalar character and
compact scalar covers for every bi-smooth coefficient, including finite sums. -/
theorem exists_centralCharacter_compactScalarSupport :
    letI := T.topology
    ∀ (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsSupercuspidal ρ → ρ.IsIrreducible →
      ∃ χ : Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier) →* ℂˣ,
        (∀ (z : Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier)) (v : V),
          ρ (z : Langlands.GeneralLinear (n + 1) F.Carrier) v = (χ z : ℂ) • v) ∧
        ∀ f : biSmoothMatrixCoefficients ρ,
          Continuous f.val ∧
          (∀ (z : Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier))
            (g : Langlands.GeneralLinear (n + 1) F.Carrier),
            f.val (z * g) = (χ z : ℂ) * f.val g) ∧
          ∃ K : Set (Langlands.GeneralLinear (n + 1) F.Carrier),
            IsCompact K ∧ Function.support f.val ⊆ scalarSaturation K := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro ρ hρ hi
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter ρ hρ.1 hi
  have := determinantNorm_ker_sup_center_finiteIndex T (n := n)
  have hsupport := biSmoothMatrixCoefficients_le_compactCentralSupportFunctions
    ρ χ hχ (T.determinantNorm (n + 1)).ker (fun ℓ w =>
      hasCompactSupport_determinantUnit_coefficient T (Nat.zero_lt_succ n)
        ρ hρ w ℓ.val ℓ.property)
  refine ⟨χ, hχ, fun f => ⟨continuous_of_mem_biSmoothMatrixCoefficients ρ _ f.property,
    biSmoothMatrixCoefficients_le_centralCovariantFunctions ρ χ hχ f.property, ?_⟩⟩
  obtain ⟨K, hK, hf⟩ := hsupport f.property
  refine ⟨K, hK, fun g hg => ?_⟩
  obtain ⟨z, k, hk, he⟩ := hf hg
  have hz : (z : Langlands.GeneralLinear (n + 1) F.Carrier) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1))).range := by
    simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar] using z.property
  obtain ⟨a, ha⟩ := hz
  exact ⟨a, k, hk, he.trans (congrArg (fun x => x * k) ha.symm)⟩

end PadicSupport

end Langlands.GodementJacquet
