import Langlands.Representation.Compact.UnitarySquareIntegrableStatements
import Langlands.Representation.MatrixCoefficient.CentralL2
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity
import Langlands.Topology.LocallyProfiniteProof

/-! # Renard IV.3.2: unitarity and semisimplicity -/

noncomputable section

open MeasureTheory

universe u v

namespace Langlands.Renard.CompactRepresentation

open HarishChandraSchwartz

section Forms

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (c : UnitaryCentralCharacter ρ) (hs : IsSmooth ρ)
  (hL2 : ∀ (ℓ : SmoothDual ρ) (x : V), MemLp (c.coefficientNorm ℓ x) 2 μ)

/-- Coefficients with a fixed vector define a linear map on the smooth dual. -/
def dualCoefficientL2Map (x : V) :
    SmoothDual ρ →ₗ[ℂ] Induction.CentralL2 c.character c.norm_eq_one μ where
  toFun ℓ := ⟨c.coefficientIntertwiner hs ℓ.val x, by
    change MemLp (Induction.centralNorm c.character c.norm_eq_one
      (c.coefficientIntertwiner hs ℓ.val x)) 2 μ
    rw [c.coefficientIntertwiner_norm hs ℓ.val x]
    exact hL2 ℓ x⟩
  map_add' ℓ k := by
    apply Induction.centralL2_ext
    intro g
    rfl
  map_smul' a ℓ := by
    apply Induction.centralL2_ext
    intro g
    rfl

/-- Pull back the central L2 form along coefficients of a cyclic generator. -/
def dualCoefficientL2Form (x : V)
    (hinj : Function.Injective (dualCoefficientL2Map μ c hs hL2 x)) :
    InvariantPositiveForm (smoothContragredient ρ) := by
  let f := dualCoefficientL2Map μ c hs hL2 x
  let b := Induction.centralL2Form c.character c.norm_eq_one μ
  refine
    { inner := fun ℓ k => b.inner (f ℓ) (f k)
      conj_inner_symm := fun ℓ k => b.conj_inner_symm (f ℓ) (f k)
      re_inner_nonneg := fun ℓ => b.re_inner_nonneg (f ℓ)
      add_left := fun ℓ k j => by rw [map_add, b.add_left]
      smul_left := fun ℓ k a => by rw [map_smul, b.smul_left]
      definite := fun ℓ h => hinj (by simpa only [map_zero] using b.definite (f ℓ) h)
      invariant := ?_ }
  intro g ℓ k
  change (∫ q, Induction.centralPairing c.character c.norm_eq_one
    (f (smoothContragredient ρ g ℓ)).val (f (smoothContragredient ρ g k)).val q ∂μ) =
    ∫ q, Induction.centralPairing c.character c.norm_eq_one (f ℓ).val (f k).val q ∂μ
  have hfun : Induction.centralPairing c.character c.norm_eq_one
      (f (smoothContragredient ρ g ℓ)).val (f (smoothContragredient ρ g k)).val =
      fun q => Induction.centralPairing c.character c.norm_eq_one (f ℓ).val (f k).val
        (QuotientGroup.mk g⁻¹ * q) := by
    funext q
    induction q using Quotient.inductionOn with
    | h a =>
      change (starRingEnd ℂ) (ℓ.val (ρ g⁻¹ (ρ a x))) * k.val (ρ g⁻¹ (ρ a x)) =
        (starRingEnd ℂ) (ℓ.val (ρ (g⁻¹ * a) x)) * k.val (ρ (g⁻¹ * a) x)
      rw [map_mul, Module.End.mul_apply]
  rw [hfun]
  exact integral_mul_left_eq_self _ (QuotientGroup.mk g⁻¹)

end Forms

section Cyclic

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

open Plancherel

/-- A cyclic subrepresentation is unitary using its forward coefficients. -/
theorem isUnitarizable_cyclic_of_forwardCoefficients
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup (Subgroup.center G) le_rfl ρ μ) (x : V) :
    IsUnitarizable (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation := by
  let S := FiniteVectors.orbitSubrepresentation ρ x
  let σ := S.toRepresentation
  have hσ := IsSquareIntegrableModCentralSubgroup.of_injective (Subgroup.center G) le_rfl μ
    hcof (ScalarSubReduction.inclusion ρ S) (ScalarSubReduction.inclusion_injective ρ S) hρ
  obtain ⟨hadm, c, hc⟩ := hσ
  have hL2 : ∀ (ℓ : SmoothDual σ) (y : S.toSubmodule), MemLp (c.coefficientNorm ℓ y) 2 μ := by
    intro ℓ y
    have hn : c.coefficientNorm ℓ y =
        centralSubgroupCoefficientNorm (Subgroup.center G) le_rfl c ℓ y := by
      funext q
      induction q using Quotient.inductionOn
      rfl
    rw [hn]
    exact hc ℓ y
  let x₀ : S.toSubmodule := ⟨x, FiniteVectors.self_mem_orbitSpan ρ x⟩
  have hinj : Function.Injective (dualCoefficientL2Map μ c hadm.1 hL2 x₀) := by
    intro ℓ k heq
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eq_zero_of_forall_orbit ρ x (ℓ.val - k.val)
    intro g
    exact sub_eq_zero.mpr (congrArg (fun f : Induction.CentralL2 c.character c.norm_eq_one μ =>
      Induction.eval _ _ f.val g) heq)
  have hXu : IsUnitarizable (smoothContragredient σ) :=
    ⟨dualCoefficientL2Form μ c hadm.1 hL2 x₀ hinj⟩
  have hXadm : IsAdmissible (smoothContragredient σ) :=
    isAdmissible_smoothContragredient_of_compact_cofinal hcof σ hadm
  exact (isUnitarizable_smoothContragredient_of_admissible hcof hXadm hXu).of_injective
    (smoothBidual hadm.1) (smoothBidual_injective_of_compact_cofinal hcof σ hadm.1)

/-- The cyclic unitary subrepresentations imply semisimplicity. -/
theorem isSemisimple_of_forwardCoefficients
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup (Subgroup.center G) le_rfl ρ μ) :
    ρ.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun x : V => Subrepresentation.asSubmodule (FiniteVectors.orbitSubrepresentation ρ x))
    (fun x => ?_) ?_
  · have hadm : IsAdmissible (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation :=
      isAdmissible_of_injective (ScalarSubReduction.inclusion ρ _)
        (ScalarSubReduction.inclusion_injective ρ _) hρ.1
    have hS := admissibleUnitarySemisimplicity G hcof _
      (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation hadm
      (isUnitarizable_cyclic_of_forwardCoefficients μ hcof hρ x)
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hS
    exact (subrepresentationAsModuleEquiv (FiniteVectors.orbitSubrepresentation ρ x)).isSemisimpleModule_iff.mp hS
  · rw [eq_top_iff]
    intro y _
    exact Submodule.mem_iSup_of_mem y (FiniteVectors.self_mem_orbitSpan ρ y)

omit [μ.IsMulRightInvariant] in
/-- The full-center specialization of the central-subgroup predicate is exact. -/
theorem squareIntegrableModCenter_iff_fullCenter :
    IsSquareIntegrableModCenter ρ μ ↔
      IsSquareIntegrableModCentralSubgroup (Subgroup.center G) le_rfl ρ μ := by
  have hn (c : UnitaryCentralCharacter ρ) (ℓ : Module.Dual ℂ V) (x : V) :
      centralSubgroupCoefficientNorm (Subgroup.center G) le_rfl c ℓ x =
        c.coefficientNorm ℓ x := by
    funext q
    induction q using Quotient.inductionOn
    rfl
  simp only [IsSquareIntegrableModCenter, IsSquareIntegrableModCentralSubgroup, hn]

/-- Glue the unitary simple summands, with only left and right Haar invariance. -/
theorem isUnitarizable_of_forwardCoefficients
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup (Subgroup.center G) le_rfl ρ μ) :
    IsUnitarizable ρ := by
  classical
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      (isSemisimple_of_forwardCoefficients μ hcof hρ)
  obtain ⟨s, hind, htop, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (R := MonoidAlgebra ℂ G)
      (M := ρ.asModule)
  let p : s → Submodule (MonoidAlgebra ℂ G) ρ.asModule := fun m => m.1
  have hint : DirectSum.IsInternal p :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ((sSupIndep_iff s).mp hind)
      (by rw [← sSup_eq_iSup']; exact htop)
  have hb : ∀ m : s, IsUnitarizable (Subrepresentation.ofSubmodule' (p m)).toRepresentation := by
    intro m
    have hinj := ScalarSubReduction.inclusion_injective ρ (Subrepresentation.ofSubmodule' (p m))
    have hsqS := IsSquareIntegrableModCentralSubgroup.of_injective (Subgroup.center G) le_rfl μ
      hcof (ScalarSubReduction.inclusion ρ (Subrepresentation.ofSubmodule' (p m))) hinj hρ
    have hi : (Subrepresentation.ofSubmodule' (p m)).toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact (subrepresentationAsModuleEquiv
        (Subrepresentation.ofSubmodule' (p m))).isSimpleModule_iff.mpr (hsimple m.1 m.2)
    obtain ⟨hadm, c, hc⟩ := (squareIntegrableModCenter_iff_fullCenter μ).mpr hsqS
    obtain ⟨ℓ, hℓ⟩ := exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcof _ hadm.1 hi
    exact ⟨c.coefficientProductForm hadm.1 hi ℓ.val hℓ μ (hc ℓ)⟩
  exact isUnitarizable_of_isInternal p hint fun m => (hb m).some

end Cyclic

/-- Renard IV.3.2, Lemma, with the exact published hypotheses. -/
theorem squareIntegrableUnitarySemisimple : SquareIntegrableUnitarySemisimpleStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ π hsq
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one
  have hρ := (squareIntegrableModCenter_iff_fullCenter μ).mp hsq
  exact ⟨isUnitarizable_of_forwardCoefficients μ hcof hρ,
    isSemisimple_of_forwardCoefficients μ hcof hρ⟩

end Langlands.Renard.CompactRepresentation
