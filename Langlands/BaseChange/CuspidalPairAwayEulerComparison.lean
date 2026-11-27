import Langlands.Automorphic.Unramified.CuspidalPairRamifiedEulerVanishing
import Langlands.BaseChange.DualSphericalSpectrumAtCompletion
import Langlands.BaseChange.GlobalHeckeNormTwistDepth
import Langlands.BaseChange.SphericalCuspidalPairCompletionEuler
import Langlands.BaseChange.WeakBaseChangeAuxiliaryTwist

/-! # Simultaneous comparison of the pair Euler factors away from one place -/

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false

universe u uQ uI

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.AdelicFunctoriality Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation LocalClassField Unramified
open scoped BigOperators NumberField FiniteExtension

section Restrictions

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {I : Type uI} (χ : I → HeckeCharacter K) (v : FinitePlace K)

private theorem inverseNormCharacterRestrictions
    (h : ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) :
    ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, (((χ i)⁻¹).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // (((χ i)⁻¹).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v)) := by
  intro w κ
  let val (i : I) := ((χ i).finiteComponent v).toMonoidHom
  have he (i : I) : (((χ i)⁻¹).finiteComponent v).toMonoidHom = κ ↔ val i = κ⁻¹ := by
    change (val i)⁻¹ = κ ↔ val i = κ⁻¹
    constructor <;> intro hx <;> apply MonoidHom.ext <;> intro y
    · exact inv_eq_iff_eq_inv.mp (DFunLike.congr_fun hx y)
    · exact inv_eq_iff_eq_inv.mpr (DFunLike.congr_fun hx y)
  have hinv : (κ⁻¹)⁻¹ = κ := MonoidHom.ext fun y => inv_inv (κ y)
  have hκ : IsNormTrivial (w.1.adicCompletion L) κ ↔ IsNormTrivial (w.1.adicCompletion L) κ⁻¹ :=
    ⟨fun a => a.inv, fun a => hinv ▸ a.inv⟩
  refine ⟨hκ.trans ((h w κ⁻¹).1.trans (exists_congr he).symm), fun h₀ => ?_⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight he)).trans ((h w κ⁻¹).2 (hκ.mp h₀))

end Restrictions

section Comparison

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)}
  {ψ' : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles L)} {r t : ℕ}
  (D : AutomorphicTwistSetup.{u,uQ} ψ r t) (U : AutomorphicTwistSetup.{u,uQ} ψ' r t)
  (I : Type uI) [Fintype I] (χ : I → HeckeCharacter K)

set_option maxHeartbeats 7000000 in
private theorem sphericalAwayPair
    (v : FinitePlace K) (μ : HeckeCharacter K)
    (h₁ : HasSphericalPowerData D.P U.P v) (h₂ : HasSphericalPowerData D.P' U.P' v)
    (hres : ∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) :
    (∀ z : ℂ, (∏ i, (D.twistedChoice (χ i * μ)).finiteL v z) =
      ∏ w : FinitePlacesAbove L v, (U.twistedChoice (μ.normComp (L := L))).finiteL w.1 z) ∧
    (∀ z : ℂ, (∏ i, (D.twistedChoice (χ i * μ)).finiteDualL v z) =
      ∏ w : FinitePlacesAbove L v, (U.twistedChoice (μ.normComp (L := L))).finiteDualL w.1 z) := by
  obtain ⟨hv₁, hw₁, hp₁⟩ := h₁
  obtain ⟨hv₂, hw₂, hp₂⟩ := h₂
  let a := D.P.spectralSystem.eigenvalues v hv₁
  let b := D.P'.spectralSystem.eigenvalues v hv₂
  let ad : Eigenvalues (r + 1) := a.map fun x => x⁻¹
  let bd : Eigenvalues (t + 1) := b.map fun x => x⁻¹
  let N := μ.normComp (L := L)
  have hN : (μ⁻¹).normComp (L := L) = N⁻¹ := ContinuousMonoidHom.ext fun _ => rfl
  constructor
  · apply sphericalCuspidalPairCompletionEuler D.P D.P' U.P U.P' D.h D.h' U.h U.h' v I χ μ a b
      (hasSphericalSpectrum_padicObject D.P D.h v hv₁)
      (hasSphericalSpectrum_padicObject D.P' D.h' v hv₂)
      (fun w => ⟨hp₁ w ▸ hasSphericalSpectrum_padicObject U.P U.h w.1 (hw₁ w),
        hp₂ w ▸ hasSphericalSpectrum_padicObject U.P' U.h' w.1 (hw₂ w)⟩) hres
      (D.additive v) (D.measure v) (D.measure_spec v) (fun w => U.additive w.1)
      (fun w => U.measure w.1) (fun w => U.measure_spec w.1)
      (fun i => (D.twistedChoice (χ i * μ)).lPolynomial v)
      (fun w => (U.twistedChoice N).lPolynomial w.1)
      (fun i => (D.finiteData_specs (χ i * μ) v).1) (fun w => (U.finiteData_specs N w.1).1)
  · refine sphericalCuspidalPairCompletionEuler D.Pd D.Pd' U.Pd U.Pd' D.hd D.hd' U.hd U.hd'
      v I (fun i => (χ i)⁻¹) μ⁻¹ ad bd
      (dualSphericalSpectrumAtCompletion K r D.T D.Td D.hTd D.P D.Pd D.h D.hd v hv₁)
      (dualSphericalSpectrumAtCompletion K t D.T' D.Td' D.hTd' D.P' D.Pd' D.h' D.hd' v hv₂)
      ?_ (inverseNormCharacterRestrictions χ v hres)
      (D.additive v) (D.measure v) (D.measure_spec v) (fun w => U.additive w.1)
      (fun w => U.measure w.1) (fun w => U.measure_spec w.1)
      (fun i => (D.twistedChoice (χ i * μ)).dualLPolynomial v)
      (fun w => (U.twistedChoice N).dualLPolynomial w.1) ?_ ?_
    · intro w
      have ha := dualSphericalSpectrumAtCompletion L r U.T U.Td U.hTd U.P U.Pd U.h U.hd w.1 (hw₁ w)
      have hb := dualSphericalSpectrumAtCompletion L t U.T' U.Td' U.hTd' U.P' U.Pd' U.h' U.hd' w.1 (hw₂ w)
      rw [hp₁ w] at ha
      rw [hp₂ w] at hb
      exact ⟨by simpa only [ad, Eigenvalues.power, Sym.map_map, Function.comp_def, inv_pow] using ha,
        by simpa only [bd, Eigenvalues.power, Sym.map_map, Function.comp_def, inv_pow] using hb⟩
    · intro i
      let C (η : HeckeCharacter K) := localClass (D.Pd.heckeDeterminantTwist η)
        (D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents η D.hd) v
      have hχd : (χ i * μ)⁻¹ = (χ i)⁻¹ * μ⁻¹ := ContinuousMonoidHom.ext fun _ => mul_inv _ _
      change IsAutomorphicPairLPolynomial (padicField v) (D.additive v) (D.measure v)
        (C ((χ i)⁻¹ * μ⁻¹)) (localClass D.Pd' D.hd' v) _
      rw [← hχd]
      exact (D.finiteData_specs (χ i * μ) v).2.1
    · intro w
      let C (η : HeckeCharacter L) := localClass (U.Pd.heckeDeterminantTwist η)
        (U.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents η U.hd) w.1
      change IsAutomorphicPairLPolynomial (padicField w.1) (U.additive w.1) (U.measure w.1)
        (C ((μ⁻¹).normComp (L := L))) (localClass U.Pd' U.hd' w.1) _
      rw [hN]
      exact (U.finiteData_specs N w.1).2.1

variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (v₀ : FinitePlace K)

/-- A common finite-order twist, trivial at the distinguished places, matches
both products of finite Euler factors at all other finite places. -/
def CuspidalPairAwayEulerComparisonStatement : Prop :=
  U.P.spectralSystem.IsArithmeticWeakBaseChangeOf D.P.spectralSystem →
  U.P'.spectralSystem.IsArithmeticWeakBaseChangeOf D.P'.spectralSystem →
  (∀ (v : FinitePlace K) (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
    (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
    (IsNormTrivial (w.1.adicCompletion L) κ →
      Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) →
  ∃ μ : HeckeCharacter K, μ.HasFiniteOrder ∧ μ.finiteComponent v₀ = 1 ∧
    (∀ w : FinitePlacesAbove L v₀, (μ.normComp (L := L)).finiteComponent w.1 = 1) ∧
    ∀ v : FinitePlace K, v ≠ v₀ →
      (∀ z : ℂ, (∏ i, (D.twistedChoice (χ i * μ)).finiteL v z) =
        ∏ w : FinitePlacesAbove L v, (U.twistedChoice (μ.normComp (L := L))).finiteL w.1 z) ∧
      (∀ z : ℂ, (∏ i, (D.twistedChoice (χ i * μ)).finiteDualL v z) =
        ∏ w : FinitePlacesAbove L v, (U.twistedChoice (μ.normComp (L := L))).finiteDualL w.1 z)

set_option maxHeartbeats 3800000 in
/-- Prescribe a high conductor at each nonspherical auxiliary place. The
spherical comparison already accounts for any common twist at good places. -/
theorem cuspidalPairAwayEulerComparison : CuspidalPairAwayEulerComparisonStatement D U I χ v₀ := by
  classical
  intro h₁ h₂ hres
  have hgood : ∀ᶠ v in Filter.cofinite, HasSphericalPowerData D.P U.P v ∧ HasSphericalPowerData D.P' U.P' v := by
    filter_upwards [h₁, h₂] with v h₁v h₂v
    obtain ⟨hv₁, hw₁, -, hp₁⟩ := h₁v
    obtain ⟨hv₂, hw₂, -, hp₂⟩ := h₂v
    exact ⟨⟨hv₁, hw₁, hp₁⟩, ⟨hv₂, hw₂, hp₂⟩⟩
  let bad := (Filter.eventually_cofinite.mp hgood).toFinset
  let S := bad.erase v₀
  choose B₁ hB₁ using fun v => cuspidalPairRamifiedEulerVanishing K D v
  choose B₂ hB₂ using fun w => cuspidalPairRamifiedEulerVanishing L U w
  obtain ⟨μ, hμ, hμ₀, hμ₀', hlevels⟩ := globalHeckeNormTwistDepth K L I χ v₀ S (Finset.notMem_erase _ _)
    (fun v _ w κ => (hres v w κ).1) B₁ B₂
  refine ⟨μ, hμ, hμ₀, hμ₀', fun v hv => ?_⟩
  by_cases hS : v ∈ S
  · have hF (i : I) := hB₁ v (χ i * μ) ((hlevels v hS).1 i)
    have hE (w : FinitePlacesAbove L v) := hB₂ w.1 (μ.normComp (L := L)) ((hlevels v hS).2 w)
    constructor
    · intro z
      simp only [FinitePairFactorChoice.finiteL, fun i => (hF i).1,
        fun w : FinitePlacesAbove L v => (hE w).1, Polynomial.eval_one, inv_one, Finset.prod_const_one]
    · intro z
      simp only [FinitePairFactorChoice.finiteDualL, fun i => (hF i).2,
        fun w : FinitePlacesAbove L v => (hE w).2, Polynomial.eval_one, inv_one, Finset.prod_const_one]
  · have hs := not_not.mp (fun hn => hS (Finset.mem_erase.mpr ⟨hv, (Set.Finite.mem_toFinset _).2 hn⟩))
    exact sphericalAwayPair D U I χ v μ hs.1 hs.2 (hres v)

end Comparison

end Langlands.BaseChange
