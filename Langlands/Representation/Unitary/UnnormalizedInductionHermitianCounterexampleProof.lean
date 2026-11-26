import Langlands.Representation.Unitary.UnnormalizedInductionHermitianCounterexampleStatement
import Langlands.Representation.Unitary.HermitianAdmissibleProof
import Langlands.Representation.Induction.ClosedSubgroupDualityProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Category.Contragredient
import Langlands.HarmonicAnalysis.RenardHomogeneousAveragingProof
import Langlands.HarmonicAnalysis.RenardHomogeneousQuotientProof
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Group.GL.ParabolicModularCharacter
import Langlands.Group.GL.CartanQuotientLawsProof
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Renard IV.2.1 counterexample using the trivial upper Borel representation -/

noncomputable section

namespace Langlands.Renard.CompactRepresentation

open Induction GeneralLinear MeasureTheory
open HarmonicAnalysis.HomogeneousFunctions
open scoped NNReal

private theorem compactInducedTrivial_fixedDual_eq_zero
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (a : H)
    (ha : relativeModular H hH a ≠ 1)
    {ℓ : SmoothDual (compactInduced H (Representation.trivial ℂ H ℂ))}
    (hℓ : ∀ g : G, smoothContragredient _ g ℓ = ℓ) : ℓ = 0 := by
  let τ := Representation.trivial ℂ H ℂ
  let δ := HarmonicAnalysis.HomogeneousFunctions.Renard.relativeCharacter H hH
  let χ := δ.toMonoidHom
  let ρ := twist χ⁻¹ τ
  have hχ (h : H) : (χ h : ℂ) = ((relativeModular H hH h : ℝ) : ℂ) := rfl
  have hχa : (χ a : ℂ) ≠ 1 := by
    intro h
    apply ha
    rw [hχ] at h
    exact_mod_cast h
  have hτ : IsSmooth τ := fun _ => ⟨⊤, fun _ => rfl⟩
  have hρ : IsSmooth ρ := (isSmooth_twist_iff _ _ (isOpen_ker_inv δ.isOpen_ker)).mpr hτ
  obtain ⟨ν, _, hν, huniq, _⟩ :=
    HarmonicAnalysis.HomogeneousFunctions.Renard.invariantFunctional G H hH
  have hν₀ : ν ≠ 0 := by
    intro hzero
    obtain ⟨c, _, hc⟩ := huniq ν hν
    have h₀ : (0 : ℂ) = c := hc 0 (by simp [hzero])
    have h₁ : (1 : ℂ) = c := hc 1 (by simp [hzero])
    exact zero_ne_one (h₀.trans h₁.symm)
  obtain ⟨e, _⟩ := closedInductionSmoothDuality G H hH χ hχ ν hν hν₀ ℂ ρ hρ
  have htwist : twist χ ρ = τ := twist_twist_inv χ τ
  rw [htwist] at e
  let f := e.symm ℓ
  have hf (g : G) : smoothInduced H (smoothContragredient ρ) g f = f := by
    calc
      _ = e.symm (smoothContragredient (compactInduced H τ) g ℓ) :=
        (Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g ℓ).symm
      _ = f := congrArg e.symm (hℓ g)
  have hconstant (g : G) : eval H _ f g = eval H _ f 1 := by
    have h := congrArg (fun F : SmoothFunctions H (smoothContragredient ρ) => eval H _ F 1) (hf g)
    change eval H _ f (1 * g) = eval H _ f 1 at h
    simpa only [one_mul] using h
  have hcov := eval_covariant H (smoothContragredient ρ) f a 1
  rw [mul_one, hconstant] at hcov
  have hvalue : eval H _ f 1 = 0 := by
    apply Subtype.ext
    change (eval H _ f 1).val = (0 : Module.Dual ℂ ℂ)
    apply LinearMap.ext
    intro x
    have hscalar : ρ a⁻¹ x = (χ a : ℂ) • x := by
      change (((χ⁻¹) a⁻¹ : ℂˣ) : ℂ) • τ a⁻¹ x = (χ a : ℂ) • x
      simp [τ]
    have h := congrArg (fun L : SmoothDual ρ => L.val x) hcov
    change (eval H _ f 1).val x = (eval H _ f 1).val (ρ a⁻¹ x) at h
    rw [hscalar, map_smul, smul_eq_mul] at h
    change (eval H _ f 1).val x = 0
    by_contra hx
    exact hχa (mul_right_cancel₀ hx (by simpa only [one_mul] using h.symm))
  have hf₀ : f = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change eval H _ f g = 0
    exact (hconstant g).trans hvalue
  calc
    ℓ = e f := (e.apply_symm_apply ℓ).symm
    _ = 0 := by
      rw [hf₀]
      exact e.toLinearEquiv.map_zero

private theorem borel_modulus_ne_one
    {p : ℕ} [Fact p.Prime] (F : PadicField p) (T : F.TopologicalData) :
    letI := T.topology
    letI := T.fieldT2
    let B := BlockShape.singletons 2
    let H := B.parabolic F.Carrier
    let hH : IsClosed (H : Set (GeneralLinear 2 F.Carrier)) := B.isClosed_parabolic F.Carrier
    letI := T.generalLinearTopologicalGroup 2
    letI := T.generalLinearLocallyCompactSpace 2
    ∃ a : H, relativeModular H hH a ≠ 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup 2
  have := T.generalLinearT2Space 2
  have := T.generalLinearLocallyCompactSpace 2
  have := LocalFieldTopology.generalLinear_secondCountableTopology F.Carrier 2
  let G := GeneralLinear 2 F.Carrier
  let B := BlockShape.singletons 2
  let H := B.parabolic F.Carrier
  have := T.parabolicLocallyCompactSpace B
  have hH : IsClosed (H : Set G) := B.isClosed_parabolic F.Carrier
  change ∃ a : H, relativeModular H hH a ≠ 1
  let exponents : Fin 2 → ℤ := fun i => if i = 0 then 1 else 0
  let a : H := CartanQuotient.representativeBorel T exponents
  have hG (g : G) : Measure.modularCharacter g = 1 := by
    let _ : MeasurableSpace G := borel G
    have _ : BorelSpace G := ⟨rfl⟩
    let μ : Measure G := RankinSelberg.generalLinearHaar F.Carrier 1
    change Measure.modularCharacterFun g = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ]
    have scalarFactor_eq_one (ν : Measure G) [ν.IsHaarMeasure] (h : ν = μ) :
        Measure.haarScalarFactor ν μ = 1 := by
      subst ν
      exact Measure.haarScalarFactor_self μ
    exact scalarFactor_eq_one _ (map_mul_right_eq_self μ g)
  have hrelative : relativeModular H hH a = Measure.modularCharacter a := by
    change HarmonicAnalysis.Distribution.renardModular (a : G) /
      HarmonicAnalysis.Distribution.renardModular a = _
    rw [HarmonicAnalysis.Distribution.renardModular_eq_inv,
      HarmonicAnalysis.Distribution.renardModular_eq_inv, hG, inv_one, one_div, inv_inv]
  have hdegree : CartanQuotient.degree exponents = 1 := by
    have h₀ : Finset.univ.filter (fun j : Fin 2 => 0 < j) = {1} := by decide
    have h₁ : Finset.univ.filter (fun j : Fin 2 => 1 < j) = ∅ := by decide
    rw [CartanQuotient.degree, Fin.sum_univ_two, h₀, h₁]
    norm_num [exponents]
  have hvalue : (relativeModular H hH a : ℝ) = (T.residueCardinality : ℝ)⁻¹ := by
    rw [hrelative, B.modularCharacter_eq (T.leviModulus B) (glBlockModulusHaar p F T 2 B)]
    change ((T.parabolicModulus B a : ℝ≥0) : ℝ) = _
    rw [← CartanQuotient.delta_eq_parabolicModulus T exponents]
    simp [CartanQuotient.delta, hdegree]
  refine ⟨a, ?_⟩
  intro ha
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  rw [ha, NNReal.coe_one] at hvalue
  exact (inv_lt_one_of_one_lt₀ hq).ne hvalue.symm

/-- Unnormalized induction of the trivial upper Borel representation of `GL₂(ℚ₂)`
has no nondegenerate invariant Hermitian form. -/
theorem unnormalizedInductionHermitianCounterexample :
    UnnormalizedInductionHermitianCounterexampleStatement := by
  intro hPreserves
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := PadicField.rational 2
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup 2
  have := T.generalLinearT2Space 2
  have := T.generalLinearLocallyCompactSpace 2
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier 2
  let G := GeneralLinear 2 F.Carrier
  let B := BlockShape.singletons 2
  let H := B.parabolic F.Carrier
  have hH : IsClosed (H : Set G) := B.isClosed_parabolic F.Carrier
  have hcompact : CompactSpace (LeftQuotient H) := Parabolic.parabolicQuotientCompact F T B
  obtain ⟨a, ha⟩ := borel_modulus_ne_one F T
  let τ := Representation.trivial ℂ H ℂ
  let π := compactInduced H τ
  have hτ : IsSmooth τ := fun _ => ⟨⊤, fun _ => rfl⟩
  obtain ⟨form, _, hnd, hinv⟩ := hPreserves G H hH hcompact ℂ τ hτ (by
    refine ⟨innerₛₗ ℂ, fun x y => (inner_conj_symm y x).symm, ?_, fun _ _ _ => rfl⟩
    intro x hx
    exact inner_self_eq_zero.mp (hx x))
  let constant : SmoothFunctions H τ :=
    smoothFunctionOf H τ (fun _ => 1) (fun _ _ => rfl) ⊤ (fun _ _ => rfl)
  let v : CompactFunctions H τ :=
    ⟨constant, (isClosed_quotientSupport H τ constant).isCompact⟩
  have hv (g : G) : π g v = v := rfl
  have hv₀ : v ≠ 0 := by
    intro h
    have he := congrArg (fun w : CompactFunctions H τ => eval H τ w.val 1) h
    exact one_ne_zero he
  let hs := compactInduced_smooth H τ
  let ℓ := HermitianProof.pairingToSmoothDual π form hinv hs v
  have hℓ (g : G) : smoothContragredient π g ℓ = ℓ := by
    rw [← HermitianProof.pairingToSmoothDual_action π form hinv hs, hv]
  have hℓ₀ := compactInducedTrivial_fixedDual_eq_zero H hH a ha hℓ
  apply hv₀
  apply HermitianProof.pairingToSmoothDual_injective π form hinv hs hnd
  simpa only [map_zero] using hℓ₀

end Langlands.Renard.CompactRepresentation
