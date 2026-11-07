import Langlands.Representation.RankinSelberg.ComponentGammaProductProof
import Langlands.Representation.RankinSelberg.CenteredBlockLPolynomialProof
import Langlands.Representation.RankinSelberg.SupercuspidalParameterProductProof
import Langlands.Representation.RankinSelberg.SegmentGammaTelescopingProof
import Langlands.Representation.RankinSelberg.SegmentBoundaryNonvanishingProof
import Langlands.Representation.RankinSelberg.GammaDecompositionUniquenessProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePoleFreeProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePairPoleOrder
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleClassification
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Classification.SegmentSpecialSquareIntegrabilityCriterionProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.SquareIntegrableCentralCharacterProof
import Langlands.Representation.Filtration.JordanHolderTransportProof

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial GeneralLinear Whittaker HarmonicAnalysis SegmentGammaTelescoping
  TemperedLFactorGamma

open scoped NNReal

universe uF uV uW uV₂ uW₂

private theorem reflectedRatio_trans {δ : ℂˣ} {P PD B BD E ED : ℂ[X]}
    (d : ReflectedRatioData δ P PD B BD) (e : ReflectedRatioData δ B BD E ED) :
    Nonempty (ReflectedRatioData δ P PD E ED) := by
  refine ⟨⟨e.coefficient * d.coefficient, e.exponent + d.exponent, ?_⟩⟩
  calc
    _ = (RatFunc.C (e.coefficient : ℂ) * (RatFunc.X : RationalFunctions) ^ e.exponent) *
        (algebraMap ℂ[X] RationalFunctions B /
          LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions BD)) := by
      rw [e.ratio]
      ring
    _ = _ := by
      rw [d.ratio]
      simp only [Units.val_mul, map_mul,
        zpow_add₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero)]
      ring

private theorem parameter_rectangle (A : Finset ℂˣ) (m n : ℕ)
    (f : ℂˣ → Fin (m + 1) → Fin (n + 1) → ℂ[X]) :
    (∏ i, ∏ j, ∏ x ∈ A, f x i j) = ∏ x ∈ A, ∏ i, ∏ j, f x i j := by
  have h (i : Fin (m + 1)) :
      (∏ j, ∏ x ∈ A, f x i j) = ∏ x ∈ A, ∏ j, f x i j := Finset.prod_comm
  simp_rw [h]
  exact Finset.prod_comm

private theorem norm_residueReflection_lt_one {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) : ‖(LocalFactor.residueReflection F : ℂ)‖ < 1 := by
  rw [LocalFactor.coe_residueReflection, norm_inv, Complex.norm_natCast]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one)

private theorem unequal_supercuspidal_one {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {a b : ℕ} (hab : a ≠ b)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W)
    (hiπ : π.IsIrreducible)
    (hsπ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π)
    (hiσ : σ.IsIrreducible)
    (hsσ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal σ)
    (hwπ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π)
    (hwσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) σ) :
    IsPadicSymmetricLPolynomial F ψ ν.val π σ 1 := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact (isPadicSymmetricLPolynomial_of_lt h).mpr
      (supercuspidalUnequalRankLFactor p F ψ ν b a σ π hiσ hsσ hwπ h)
  · exact (isPadicSymmetricLPolynomial_of_le h.le).mpr
      (supercuspidalUnequalRankLFactor p F ψ ν a b π σ hiπ hsπ hwσ h)

section Normalization

universe uG uX uY uZ

private theorem component_twist {G : Type uG} [Group G]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {V : Type uY} [AddCommGroup V] [Module ℂ V]
    {ξ : Representation ℂ G X} {π : Representation ℂ G V}
    (χ : G →* ℂˣ) (hc : IsIrreducibleComponent ξ π) :
    IsIrreducibleComponent (twist χ ξ) (twist χ π) := by
  obtain ⟨hi, U, f, hf⟩ := hc
  refine ⟨(isIrreducible_twist_iff χ π).mpr hi, twistSubrepresentation χ U,
    (twistIntertwining χ f).comp
      (twistSubrepresentationEquiv χ U).symm.toIntertwiningMap, ?_⟩
  exact hf

private theorem component_ambient_equiv {G : Type uG} [Group G]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    {V : Type uZ} [AddCommGroup V] [Module ℂ V]
    {ξ : Representation ℂ G X} {η : Representation ℂ G Y}
    {π : Representation ℂ G V} (e : ξ.Equiv η)
    (hc : IsIrreducibleComponent ξ π) : IsIrreducibleComponent η π := by
  obtain ⟨hi, U, f, hf⟩ := hc
  let eU : U.toRepresentation.Equiv
      (JordanHolderTransportProof.mapSub e U).toRepresentation :=
    { toLinearEquiv := JordanHolderTransportProof.upperEquiv e U
      isIntertwining' := fun g => by
        ext v
        change e.toLinearEquiv (ξ g v.val) = η g (e.toLinearEquiv v.val)
        exact JordanHolderTransportProof.equiv_apply_rep e g v.val }
  refine ⟨hi, JordanHolderTransportProof.mapSub e U,
    f.comp eU.symm.toIntertwiningMap, ?_⟩
  exact hf.comp eU.symm.surjective

private theorem centeredSegmentBlocks_twist {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) {a : ℕ} (m : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V)
    (s : ℝ) (i : Fin (m + 1)) :
    realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) s
        (centeredSegmentBlocks F m π₀ i) =
      centeredSegmentBlocks F m
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) s π₀) i := by
  simp only [centeredSegmentBlocks, ← realPowerTwist_add]
  rw [add_comm s]

private theorem component_centered_twist {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) {a m r : ℕ}
    (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
    {V : Type uV₂} [AddCommGroup V] [Module ℂ V]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (s : ℝ) (hc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π) :
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m
          (realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) s π₀)))
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) s π) := by
  let := F.canonicalTopologicalData.topology
  let e := F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv
    (succBlockShape (fun _ => a) hr) (realTwistCharacter F s) (centeredSegmentBlocks F m π₀)
  have heblocks :
      (fun i => twist ((realTwistCharacter F s).toMonoidHom.comp determinant)
        (centeredSegmentBlocks F m π₀ i)) =
      centeredSegmentBlocks F m
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) s π₀) := by
    funext i
    exact centeredSegmentBlocks_twist F m π₀ s i
  have hc' := component_ambient_equiv e
    (component_twist (F.canonicalTopologicalData.determinantPowerCharacter (r + 1) s) hc)
  change IsIrreducibleComponent
    (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
      (fun i => twist ((realTwistCharacter F s).toMonoidHom.comp determinant)
        (centeredSegmentBlocks F m π₀ i)))
    (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) s π) at hc'
  rw [heblocks] at hc'
  exact hc'

private theorem component_scalarCharacter {G : Type uG} [Group G]
    {C : Type uZ} [Group C] {z : C →* G} {ω : C →* ℂˣ}
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {V : Type uY} [AddCommGroup V] [Module ℂ V]
    {ξ : Representation ℂ G X} {π : Representation ℂ G V}
    (hc : IsIrreducibleComponent ξ π)
    (h : Classification.HasScalarCharacter ξ z ω) :
    Classification.HasScalarCharacter π z ω := by
  obtain ⟨-, U, f, hf⟩ := hc
  have hU : Classification.HasScalarCharacter U.toRepresentation z ω := by
    intro c v
    apply Subtype.ext
    exact h c v.val
  intro c v
  obtain ⟨u, rfl⟩ := hf v
  change π (z c) (f u) = (ω c : ℂ) • f u
  rw [← f.isIntertwining, hU c u, map_smul]

private theorem centered_scalarCharacter_product {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (a m : ℕ) (ω : F.Carrierˣ →* ℂˣ) :
    (∏ i : Fin (m + 1), (ω *
      (F.canonicalTopologicalData.determinantPowerCharacter (a + 1)
        ((m : ℝ) / 2 - (i : ℕ))).comp GeneralLinear.scalar)) = ω ^ (m + 1) := by
  classical
  ext x
  have hpos : (0 : ℝ) <
      ((F.canonicalTopologicalData.normalizedAbsUnits x : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
      (F.canonicalTopologicalData.normalizedAbsUnits x).ne_zero)
  have he : ∑ i : Fin (m + 1), ((m : ℝ) / 2 - (i : ℕ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Classification.sum_fin_val_real]
    push_cast
    ring
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, MonoidHom.pow_apply,
    Units.val_pow_eq_pow_val]
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply,
    PadicField.TopologicalData.coe_determinantPowerCharacter_scalar]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.ofReal_prod, ← Real.rpow_sum_of_pos hpos, ← Finset.mul_sum, he,
    mul_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

private theorem squareIntegrable_centered_component {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) {a m r : ℕ}
    (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
    {V : Type uV₂} [AddCommGroup V] [Module ℂ V]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hqπ₀ : F.canonicalTopologicalData.IsSquareIntegrable π₀)
    (hess : F.canonicalTopologicalData.IsEssentiallySquareIntegrable π)
    (hc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π) :
    F.canonicalTopologicalData.IsSquareIntegrable π := by
  classical
  let := F.canonicalTopologicalData.topology
  let : π.IsIrreducible := hc.1
  let : Nontrivial V := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)) π.asModule
  obtain ⟨c⟩ := nonempty_unitaryCentralCharacter_of_isSquareIntegrable
    F.canonicalTopologicalData hqπ₀
  let ω : F.Carrierˣ →* ℂˣ := c.character.comp GeneralLinear.scalarToCenter
  have hω : Classification.HasScalarCharacter π₀ GeneralLinear.scalar ω :=
    fun x v => c.acts (GeneralLinear.scalarToCenter x) v
  have hind := F.canonicalTopologicalData.hasScalarCharacter_normalizedProductInduced
    (succBlockShape (fun _ => a) hr)
    (fun i : Fin (m + 1) => Classification.hasScalarCharacter_twist
      (F.canonicalTopologicalData.determinantPowerCharacter (a + 1)
        ((m : ℝ) / 2 - (i : ℕ))) hω)
  rw [centered_scalarCharacter_product] at hind
  have hact : Classification.HasScalarCharacter π GeneralLinear.scalar (ω ^ (m + 1)) :=
    component_scalarCharacter hc hind
  have hadm : IsAdmissible π := by
    obtain ⟨s, hs⟩ := hess
    exact (isAdmissible_twist_iff
      (F.canonicalTopologicalData.determinantPowerCharacter (r + 1) (-s)) π
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (r + 1) (-s))).mp
        hs.isAdmissible
  obtain ⟨d⟩ := (glSquareIntegrableCentralCharacter p F F.canonicalTopologicalData
    (r + 1) (Nat.succ_pos r) V π (ω ^ (m + 1)) hadm hact).2.1.mpr (by
      intro x
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, norm_pow]
      change ‖(c.character (GeneralLinear.scalarToCenter x) : ℂ)‖ ^ (m + 1) = 1
      rw [c.norm_eq_one, one_pow])
  exact Classification.isSquareIntegrable_of_essential_of_unitaryCentralCharacter
    F.canonicalTopologicalData (Nat.succ_pos r) hess d

end Normalization

/-- The centered formula when the two bases and the actual components are
square-integrable. -/
theorem squareIntegrableLFactor_normalized {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a m r b n t : ℕ) (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (ht : ∑ _j : Fin (n + 1), (b + 1) = t + 1)
    {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
    {W₀ : Type uW} [AddCommGroup W₀] [Module ℂ W₀]
    {V : Type uV₂} [AddCommGroup V] [Module ℂ V]
    {W : Type uW₂} [AddCommGroup W] [Module ℂ W]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀)
    (σ₀ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W₀)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hiπ₀ : π₀.IsIrreducible)
    (hsπ₀ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π₀)
    (hiσ₀ : σ₀.IsIrreducible)
    (hsσ₀ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal σ₀)
    (hqπ₀ : F.canonicalTopologicalData.IsSquareIntegrable π₀)
    (hqσ₀ : F.canonicalTopologicalData.IsSquareIntegrable σ₀)
    (hqπ : F.canonicalTopologicalData.IsSquareIntegrable π)
    (hcπ : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π)
    (hqσ : F.canonicalTopologicalData.IsSquareIntegrable σ)
    (hcσ : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => b) ht)
        (centeredSegmentBlocks F n σ₀)) σ)
    (htr : t ≤ r) :
    ∃ (P : ℂ[X]) (Q : Fin (n + 1) → ℂ[X]),
      IsPadicPairLPolynomial F ψ ν.val π σ P ∧
      (∀ j, IsPadicSymmetricLPolynomial F ψ ν.val
        (centeredSegmentBlocks F m π₀ 0) (centeredSegmentBlocks F n σ₀ j) (Q j)) ∧
      P = ∏ j, Q j := by
  classical
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hwπ := squareIntegrableWhittakerType_of_genericity F
    (Classification.squareIntegrableGenericity F F.canonicalTopologicalData) ψ r π hcπ.1 hqπ
  have hwσ := squareIntegrableWhittakerType_of_genericity F
    (Classification.squareIntegrableGenericity F F.canonicalTopologicalData) ψ t σ hcσ.1 hqσ
  have hwπ₀ := squareIntegrableWhittakerType_of_genericity F
    (Classification.squareIntegrableGenericity F F.canonicalTopologicalData) ψ a π₀ hiπ₀ hqπ₀
  have hwσ₀ := squareIntegrableWhittakerType_of_genericity F
    (Classification.squareIntegrableGenericity F F.canonicalTopologicalData) ψ b σ₀ hiσ₀ hqσ₀
  have hwbπ (i : Fin (m + 1)) : IsOfWhittakerType a (standardCharacter ψ a)
      (centeredSegmentBlocks F m π₀ i) := by
    apply (isOfWhittakerType_twist_iff _ _ π₀
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (a + 1)
        ((m : ℝ) / 2 - (i : ℕ))) _).mpr hwπ₀
    intro u
    simpa only [PadicField.TopologicalData.determinantPowerCharacter,
      PadicField.TopologicalData.determinantNorm, realPowerCharacter,
      MonoidHom.comp_assoc] using
      determinantCharacter_unipotent
        (realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits
          ((m : ℝ) / 2 - (i : ℕ))) u
  have hwbσ (j : Fin (n + 1)) : IsOfWhittakerType b (standardCharacter ψ b)
      (centeredSegmentBlocks F n σ₀ j) := by
    apply (isOfWhittakerType_twist_iff _ _ σ₀
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (b + 1)
        ((n : ℝ) / 2 - (j : ℕ))) _).mpr hwσ₀
    intro u
    simpa only [PadicField.TopologicalData.determinantPowerCharacter,
      PadicField.TopologicalData.determinantNorm, realPowerCharacter,
      MonoidHom.comp_assoc] using
      determinantCharacter_unipotent
        (realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits
          ((n : ℝ) / 2 - (j : ℕ))) u
  obtain ⟨P, hP, hnP⟩ := squareIntegrablePoleFree p F ψ ν r t π σ hcπ.1 hqπ hcσ.1 hqσ
  have hiπd : (inverseTransposePullback π).IsIrreducible :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff π
      (inverseTranspose (r + 1) F.Carrier)).mpr hcπ.1
  have hiσd : (inverseTransposePullback σ).IsIrreducible :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff σ
      (inverseTranspose (t + 1) F.Carrier)).mpr hcσ.1
  have hqπd : F.canonicalTopologicalData.IsSquareIntegrable (inverseTransposePullback π) :=
    F.canonicalTopologicalData.isSquareIntegrable_comp_continuousMulEquiv π
      (F.canonicalTopologicalData.generalLinearInverseTranspose (r + 1)) hqπ
  have hqσd : F.canonicalTopologicalData.IsSquareIntegrable (inverseTransposePullback σ) :=
    F.canonicalTopologicalData.isSquareIntegrable_comp_continuousMulEquiv σ
      (F.canonicalTopologicalData.generalLinearInverseTranspose (t + 1)) hqσ
  obtain ⟨PD, hPD, hnPD⟩ := squareIntegrablePoleFree p F (ψ.scale (-1))
    (DominantRankTransport.negatedSelfDualHaar F ψ ν) r t
    (inverseTransposePullback π) (inverseTransposePullback σ) hiπd hqπd hiσd hqσd
  obtain ⟨A, hA, hbase, hbased, horder⟩ : ∃ A : Finset ℂˣ,
      (∀ x ∈ A, ‖(x : ℂ)‖ = 1) ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π₀ σ₀ (∏ x ∈ A, linearFactor x) ∧
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback π₀) (inverseTransposePullback σ₀)
        (∏ x ∈ A, linearFactor x⁻¹) ∧
      (A.Nonempty → n ≤ m) := by
    rcases eq_or_ne a b with rfl | hab
    · obtain ⟨A, _, hbase, hbased, hnorm⟩ := supercuspidalParameterProduct p F ψ ν a π₀ σ₀
        hiπ₀ hsπ₀ hiσ₀
        hwσ₀
      refine ⟨A, hnorm
        (glSquareIntegrableUnitarity p F F.canonicalTopologicalData (a + 1) (by omega)
          V₀ π₀ hiπ₀ hqπ₀)
        (glSquareIntegrableUnitarity p F F.canonicalTopologicalData (a + 1) (by omega)
          W₀ σ₀ hiσ₀ hqσ₀), ?_, ?_, fun _ => (le_iff_of_centeredSegment_rank hr ht).mp htr⟩
      · exact (isPadicSymmetricLPolynomial_of_le (le_refl a)).mpr hbase
      · exact (isPadicSymmetricLPolynomial_of_le (le_refl a)).mpr hbased
    · refine ⟨∅, by simp, ?_, ?_, by simp⟩
      · simpa using unequal_supercuspidal_one ν hab π₀ σ₀ hiπ₀ hsπ₀ hiσ₀ hsσ₀ hwπ₀ hwσ₀
      · have hidπ : (inverseTransposePullback π₀).IsIrreducible :=
          (CuspidalSupport.isIrreducible_comp_mulEquiv_iff π₀
            (inverseTranspose (a + 1) F.Carrier)).mpr hiπ₀
        have hidσ : (inverseTransposePullback σ₀).IsIrreducible :=
          (CuspidalSupport.isIrreducible_comp_mulEquiv_iff σ₀
            (inverseTranspose (b + 1) F.Carrier)).mpr hiσ₀
        simpa only [Finset.prod_empty, DominantRankTransport.negatedSelfDualHaar_val] using unequal_supercuspidal_one
          (DominantRankTransport.negatedSelfDualHaar F ψ ν) hab
          (inverseTransposePullback π₀) (inverseTransposePullback σ₀) hidπ
          (isSupercuspidal_comp_inverseTranspose π₀ hsπ₀) hidσ
          (isSupercuspidal_comp_inverseTranspose σ₀ hsσ₀)
          (by simpa only [standardCharacter_scale_neg_one] using
            isOfWhittakerType_inverseTransposePullback ψ π₀ hwπ₀)
          (by simpa only [standardCharacter_scale_neg_one] using
            isOfWhittakerType_inverseTransposePullback ψ σ₀ hwσ₀)
  let c := centeredHalfShiftUnit F
  let Q (i : Fin (m + 1)) (j : Fin (n + 1)) : ℂ[X] :=
    ∏ x ∈ A, linearFactor (x * c ^ blockExponent m n i.val j.val)
  let QD (i : Fin (m + 1)) (j : Fin (n + 1)) : ℂ[X] :=
    ∏ x ∈ A, linearFactor (x⁻¹ * c ^ (-blockExponent m n i.val j.val))
  have hcert := centeredBlockLPolynomial p F ψ ν a b m n π₀ σ₀ _ _ hbase hbased
  have hQ (i j) : IsPadicSymmetricLPolynomial F ψ ν.val
      (centeredSegmentBlocks F m π₀ i) (centeredSegmentBlocks F n σ₀ j) (Q i j) := by
    simpa only [polynomialRescale_parameterProduct] using (hcert i j).1
  have hQD (i j) : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback (centeredSegmentBlocks F m π₀ i))
      (inverseTransposePullback (centeredSegmentBlocks F n σ₀ j)) (QD i j) := by
    simpa only [map_prod, polynomialRescale_linearFactor] using (hcert i j).2
  obtain ⟨d⟩ := componentGammaProduct p F ψ ν r t (m + 1) (n + 1)
    (fun _ => a) (fun _ => b) hr ht
    (centeredSegmentBlocks F m π₀) (centeredSegmentBlocks F n σ₀) π σ
    hwbπ hwbσ hwπ hwσ hcπ hcσ P PD Q QD hP hQ hPD hQD
  have hfull : (∏ i, ∏ j, Q i j) = ∏ x ∈ A, fullPolynomial x c m n :=
    parameter_rectangle A m n _
  have hfulld : (∏ i, ∏ j, QD i j) = ∏ x ∈ A, fullPolynomial x⁻¹ c⁻¹ m n := by
    rw [show (∏ i, ∏ j, QD i j) =
      ∏ x ∈ A, ∏ i : Fin (m + 1), ∏ j : Fin (n + 1),
        linearFactor (x⁻¹ * c ^ (-blockExponent m n i.val j.val)) from
          parameter_rectangle A m n _]
    simp only [fullPolynomial, inv_zpow, zpow_neg]
  rw [hfull, hfulld] at d
  obtain ⟨e⟩ := segmentGammaTelescoping A c m n
  rw [show c ^ (2 : ℕ) = LocalFactor.residueReflection F from centeredHalfShiftUnit_sq F] at e
  obtain ⟨f⟩ := reflectedRatio_trans d e
  have hnB (z : ℂ) (hz : ‖z‖ < 1) :
      (∏ x ∈ A, boundaryPolynomial x c m n).eval z ≠ 0 := by
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun x hx => boundaryPolynomial_eval_ne_zero x c
      (horder ⟨x, hx⟩) (norm_centeredHalfShiftUnit_le_one F) (hA x hx).le z hz
  have hnBD (z : ℂ) (hz : ‖z‖ < 1) :
      (∏ x ∈ A, boundaryPolynomial x⁻¹ c m n).eval z ≠ 0 := by
    rw [eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    apply boundaryPolynomial_eval_ne_zero x⁻¹ c (horder ⟨x, hx⟩)
      (norm_centeredHalfShiftUnit_le_one F) _ z hz
    simp [hA x hx]
  have heq : P = ∏ x ∈ A, boundaryPolynomial x c m n :=
    gammaDecompositionUniqueness_of_ratio 1 1 (LocalFactor.residueReflection F)
      f.coefficient f.exponent P PD _ _ (by norm_num) (by norm_num)
      (by simpa using norm_residueReflection_lt_one F)
      hP.coeff_zero (by rw [coeff_zero_eq_eval_zero, eval_prod]; simp [← coeff_zero_eq_eval_zero])
      hnP hnB hnPD hnBD f.ratio
  refine ⟨P, Q 0, (isPadicSymmetricLPolynomial_of_le htr).mp hP, hQ 0, ?_⟩
  rw [heq]
  exact Finset.prod_comm

/-- JPSS 1983, Theorem (8.2), display (5), with arbitrary independent field and
representation-carrier universes. -/
theorem squareIntegrableLFactor :
    SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW₂} := by
  intro p _ F ψ ν a m r b n t hr ht V₀ _ _ W₀ _ _ V _ _ W _ _
    π₀ σ₀ π σ hiπ₀ hsπ₀ hiσ₀ hsσ₀ hessπ hcπ hessσ hcσ htr
  let := F.canonicalTopologicalData.topology
  obtain ⟨s, hs⟩ := supercuspidal_isEssentiallySquareIntegrable F a
    (SmoothRep.of π₀ hsπ₀.1.1) hiπ₀ hsπ₀
  obtain ⟨z, hz⟩ := supercuspidal_isEssentiallySquareIntegrable F b
    (SmoothRep.of σ₀ hsσ₀.1.1) hiσ₀ hsσ₀
  let π₀' := realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) (-s) π₀
  let σ₀' := realPowerTwist (F.canonicalTopologicalData.determinantNorm (b + 1)) (-z) σ₀
  let π' := realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) (-s) π
  let σ' := realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) (-z) σ
  have hcπ' := component_centered_twist F hr π₀ π (-s) hcπ
  have hcσ' := component_centered_twist F ht σ₀ σ (-z) hcσ
  have hqπ' := squareIntegrable_centered_component F hr π₀' π' hs
    (hessπ.realPowerTwist (-s)) hcπ'
  have hqσ' := squareIntegrable_centered_component F ht σ₀' σ' hz
    (hessσ.realPowerTwist (-z)) hcσ'
  have hiπ₀' : π₀'.IsIrreducible := (isIrreducible_twist_iff _ π₀).mpr hiπ₀
  have hiσ₀' : σ₀'.IsIrreducible := (isIrreducible_twist_iff _ σ₀).mpr hiσ₀
  have hsπ₀' : IsSupercuspidal π₀' :=
    (isSupercuspidal_realPowerTwist_iff (a + 1) (-s) π₀).mpr hsπ₀
  have hsσ₀' : IsSupercuspidal σ₀' :=
    (isSupercuspidal_realPowerTwist_iff (b + 1) (-z) σ₀).mpr hsσ₀
  obtain ⟨P, Q, hP, hQ, hprod⟩ := squareIntegrableLFactor_normalized F ψ ν
    a m r b n t hr ht π₀' σ₀' π' σ' hiπ₀' hsπ₀' hiσ₀' hsσ₀'
    hs hz hqπ' hcπ' hqσ' hcσ' htr
  let S := realTwistPolynomial F s
  let Z := realTwistPolynomial F z
  refine ⟨Z (S P), fun j => Z (S (Q j)), ?_, ?_, ?_⟩
  · have htw := IsPadicRankLPolynomial.twist_real F ψ ν
      (n := r + 1) (t := t + 1)
      ((isPadicSymmetricLPolynomial_of_le htr).mpr hP) s z
    apply (isPadicSymmetricLPolynomial_of_le htr).mp
    simpa only [π', σ', realPowerTwist_cancel_neg] using
      (isPadicRankLPolynomial_succ (r := r) (k := t)).mp htw
  · intro j
    have htw := IsPadicRankLPolynomial.twist_real F ψ ν
      (n := a + 1) (t := b + 1) (hQ j) s z
    simpa only [centeredSegmentBlocks_twist, π₀', σ₀',
      realPowerTwist_cancel_neg] using
        (isPadicRankLPolynomial_succ (r := a) (k := b)).mp htw
  · rw [hprod, map_prod, map_prod]

end Langlands.RankinSelberg
