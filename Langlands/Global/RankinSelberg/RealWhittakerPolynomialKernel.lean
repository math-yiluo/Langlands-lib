import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Representation.Archimedean.BGChaseReps
import Langlands.Representation.Archimedean.RealLeftPolynomialGrowthProof
import Langlands.Representation.Archimedean.RealStandardCentralGrowth
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof

/-! # Exact Whittaker vanishing on lower-root-polynomial submodules -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Algebra.UniversalEnveloping
open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealLocalWhittaker

open RealIwasawa RealPrincipalSeriesDuality
open RealWhittakerGauge (hasDerivAt_realScaledCharacter)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}
local notation "n" => (r + 1)
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation:max "V" ds:max => Automorphic.realStandardKFinite n ds

private theorem rightDerivative_upper_torus {a : ℝˣ} {W : G → ℂ}
    (hW : W ∈ regularFunctions r a) (y : Fin n → ℝ) {X : M}
    (hX : ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) :
    rightDerivative (matrixModel ℝ n) X W (torus y) =
      (2 * Real.pi * (a : ℝ) * Complex.I) *
        ((∑ i : Fin r, Real.exp (y i.castSucc - y i.succ) * X i.castSucc i.succ : ℝ) : ℂ) *
        W (torus y) := by
  let Y : M := fun i j => Real.exp (y i - y j) * X i j
  let d := torus y
  have hY : Y.IsUpperTriangular := fun i j hij =>
    mul_eq_zero_of_right _ (hX i j (le_of_lt hij))
  have hYdiag : ∀ i, Y i i = 0 := fun i => by simp [Y, hX i i le_rfl]
  let u := unipotentLine Y hY hYdiag
  let γ (t : ℝ) := (1 + t • Y) * d.val
  have hmul : Y * d.val = d.val * X := by
    ext i j
    rw [show d.val = Matrix.diagonal (fun k => Real.exp (y k)) by exact torus_val y,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    dsimp [Y]
    rw [Real.exp_sub]
    field_simp
  have hγ : HasDerivAt γ (d.val * X) 0 := by
    rw [← hmul]
    simpa only [γ, id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const Y).const_add (1 : M)).mul_const d.val
  have hγ₀ : γ 0 = d.val := by simp [γ]
  have hcomp := (differentiableAt_unitsExtension hW.2.1 (Units.isUnit d)).hasFDerivAt
  rw [← hγ₀] at hcomp
  have hvalue := hcomp.comp_hasDerivAt 0 hγ
  rw [hγ₀, ← rightDerivative_eq_fderiv hW.2.1] at hvalue
  let b : ℝ := ∑ i : Fin r, Y i.castSucc i.succ
  have heq : (fun t => unitsExtension W (γ t)) =
      fun t => (realScaledCharacter a).complex (t * b) * W d := by
    funext t
    change unitsExtension W ((u t).val * d).val = _
    rw [unitsExtension_val, hW.1 (u t).val (u t).property d, realWhittakerCharacter]
    congr 2
    change (∑ i : Fin r, (1 + t • Y) i.castSucc i.succ) = t * b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne]
  change HasDerivAt (fun t => unitsExtension W (γ t)) _ 0 at hvalue
  rw [heq] at hvalue
  have hb : HasDerivAt (fun t : ℝ => t * b) b 0 := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const b
  have ha : HasDerivAt (fun s : ℝ => (realScaledCharacter a).complex s)
      (2 * Real.pi * (a : ℝ) * Complex.I) (0 * b) := by
    rw [zero_mul]
    exact hasDerivAt_realScaledCharacter a
  have hc := ha.scomp 0 hb
  have hc' : HasDerivAt (fun t : ℝ => (realScaledCharacter a).complex (t * b) * W d)
      ((2 * Real.pi * (a : ℝ) * Complex.I) * (b : ℂ) * W d) 0 := by
    apply (hc.mul_const (W d)).congr_deriv
    rw [Complex.real_smul]
    ring
  exact hvalue.unique hc'

private theorem exists_generic_of_ne_zero_on {ds : List RealBlock} {a : ℝˣ}
    (Y : Submodule ℂ (V ds))
    (hY : IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) Y)
    {B : (V ds) →ₗ[ℂ] (G → ℂ)} (hB : IsRealWhittakerIntertwiner r ds a B)
    {v : V ds} (hv : v ∈ Y) {g : G} (hg : B v g ≠ 0) :
    @IsRealGenericGKModule n ↥Y _ _ (BGChase.restrictLie (realStandardLie n ds) Y hY.2) := by
  let y := alpha g
  let k := kpart g
  let ku : Matrix.unitaryGroup (Fin n) ℝ := ⟨k.val.val, k.property⟩
  have hk : Unitary.toUnits ku = k.val := Units.ext rfl
  let v' : Y := ⟨realStandardRep n ds ku v, hY.1 ku v hv⟩
  have hv' : B v' (torus y) ≠ 0 := by
    have h := hB.2.2.2.1 k v v' (by
      change ((realStandardRep n ds ku v : V ds) : G → ℂ) = _
      rw [realStandardRep_apply_coe, hk])
    have hdec := npart_mul_torus_mul_kpart g
    rw [← hdec, mul_assoc, hB.1 v _ (npart g).property] at hg
    intro hzero
    apply hg
    have h' := congrFun h (torus y)
    change B v' (torus y) = B v (torus y * k.val) at h'
    rw [← h', hzero, mul_zero]
  let ℓ := (LinearMap.proj (torus y)).comp (B.comp Y.subtype)
  have hℓ : ℓ ≠ 0 := fun h => hv' (LinearMap.congr_fun h v')
  let c (i : Fin n) : ℝ :=
    if hi : i.val + 1 < n then
      2 * Real.pi * (a : ℝ) * Real.exp (y i - y ⟨i.val + 1, hi⟩)
    else 0
  refine ⟨ℓ, hℓ, c, ?_, ?_⟩
  · intro i hi
    dsimp only [c]
    rw [dite_eq_left hi]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) a.ne_zero)
      (Real.exp_ne_zero _)
  · intro X hX w
    change B (realStandardLie n ds (1 ⊗ₜ[ℝ] X) w.val) (torus y) = _
    have h := hB.2.2.2.2 X w.val (realStandardLie n ds (1 ⊗ₜ[ℝ] X) w.val)
      (realStandardLie_one_tmul_apply_coe n ds X w.val)
    rw [h, rightDerivative_upper_torus
      (show B w.val ∈ regularFunctions r a from
        ⟨hB.1 w.val, hB.2.1 w.val, HasPolynomialGrowth.of_bound (hB.2.2.1 w.val)⟩) y hX]
    have hSum : (∑ i : Fin n, ∑ j : Fin n,
        if j.val = i.val + 1 then c i * X i j else 0) =
        (2 * Real.pi * (a : ℝ)) *
          ∑ i : Fin r, Real.exp (y i.castSucc - y i.succ) * X i.castSucc i.succ := by
      rw [Fin.sum_univ_castSucc, Finset.mul_sum]
      have hl : (∑ j : Fin n, if j.val = (Fin.last r).val + 1
          then c (Fin.last r) * X (Fin.last r) j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj : j.val ≠ (Fin.last r).val + 1 := by
          simp only [Fin.val_last]
          exact j.isLt.ne
        rw [ite_eq_right hj]
      rw [hl, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i.succ]
      · have hi : i.val + 1 < r + 1 := i.succ.isLt
        simp only [Fin.val_succ, Fin.val_castSucc, ite_true, c, dite_eq_left hi, mul_assoc]
        rfl
      · intro j _ hj
        have hj' : j.val ≠ i.castSucc.val + 1 := fun he => hj (Fin.ext he)
        rw [ite_eq_right hj']
      · simp
    change _ = (Complex.I * _) * B w.val (torus y)
    rw [hSum]
    push_cast
    ring

/-- An invariant submodule that is polynomial in one lower-root direction contributes
zero under every exact Whittaker coefficient map. -/
def RealWhittakerLeftPolynomialVanishingStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (p k : ℕ) (hp : p + 1 < r + 1)
    (Y : Submodule ℂ (Automorphic.realStandardKFinite (r + 1) ds)),
    IsGKSubmodule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds) Y →
    (∀ f ∈ Y, ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
      ∃ q : Polynomial ℂ, q.degree < k ∧ ∀ t : ℝ,
        f.val (lowerRootElement (r + 1) p hp t * g) = q.eval (t : ℂ)) →
    ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
      IsRealWhittakerIntertwiner r ds a B → Y ≤ LinearMap.ker B

private theorem mem_centralIdeal_of_vanishes_on_subspace
    {𝔤 E : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [AddCommGroup E] [Module ℂ E]
    (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ E) (Y : Submodule ℂ E)
    (hLie : ∀ X w, w ∈ Y → π X w ∈ Y)
    (hπ : HasInfinitesimalCharacter π)
    (hMF : HasInfinitesimalCharacter (BGChase.restrictLie π Y hLie) →
      IsMaximallyFaithful (BGChase.restrictLie π Y hLie))
    {v : E} (hv : v ∈ Y) (hv₀ : v ≠ 0)
    (u : UniversalEnvelopingAlgebra ℂ 𝔤) (hu : ∀ w : Y, envelopingAction π u w.val = 0) :
    u ∈ Ideal.span {z | z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤) ∧
      envelopingAction π z = 0} := by
  let σ := BGChase.restrictLie π Y hLie
  have hComp (z : UniversalEnvelopingAlgebra ℂ 𝔤) (w : Y) :
      ((envelopingAction σ z w : Y) : E) = envelopingAction π z w.val :=
    envelopingAction_intertwine σ π Y.subtype (fun _ _ => rfl) z w
  have hInf : @HasInfinitesimalCharacter _ _ _ ↥Y _ _ σ := by
    intro z hz
    obtain ⟨c, hc⟩ := hπ z hz
    refine ⟨c, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [hComp, hc]
    rfl
  have hZero : envelopingAction σ u = 0 :=
    LinearMap.ext fun w => Subtype.ext ((hComp u w).trans (hu w))
  apply Ideal.span_mono _ (hMF hInf u hZero)
  rintro z ⟨hz, hz₀⟩
  refine ⟨hz, ?_⟩
  obtain ⟨c, hc⟩ := hπ z hz
  have hZ := hComp z ⟨v, hv⟩
  rw [hz₀, LinearMap.zero_apply, hc] at hZ
  have hcv : c • v = 0 := hZ.symm
  rw [(smul_eq_zero.mp hcv).resolve_right hv₀, map_zero] at hc
  exact hc

private theorem maximallyFaithful_of_generic (m : ℕ) {E : Type} [AddCommGroup E] [Module ℂ E]
    (σ : (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ E)
    (hGen : IsRealGenericGKModule m σ) :
    HasInfinitesimalCharacter σ → IsMaximallyFaithful σ :=
  fun hInf => Kostant.realWhittakerMaximallyFaithful m E σ hInf hGen

set_option backward.isDefEq.respectTransparency true in
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem realWhittakerLeftPolynomialVanishing : RealWhittakerLeftPolynomialVanishingStatement := by
  intro r ds p k hp Y hY hPol a B hB v hv
  let _ : AddCommGroup ↥(Automorphic.realStandardKFinite (r + 1) ds) :=
    (Automorphic.realStandardKFinite (r + 1) ds).addCommGroup
  let _ : Module ℂ ↥(Automorphic.realStandardKFinite (r + 1) ds) :=
    (Automorphic.realStandardKFinite (r + 1) ds).module
  let _ : AddCommGroup ↥Y := Y.addCommGroup
  let _ : Module ℂ ↥Y := Y.module
  rw [LinearMap.mem_ker]
  funext g
  change B v g = 0
  by_contra hg
  have hv₀ : v ≠ 0 := by
    intro h
    apply hg
    rw [h, map_zero, Pi.zero_apply]
  let π := realStandardLie (r + 1) ds
  let σ := BGChase.restrictLie π Y hY.2
  have hGen : @IsRealGenericGKModule (r + 1) ↥Y _ _ σ :=
    exists_generic_of_ne_zero_on Y hY hB hv hg
  have hFaithful := @maximallyFaithful_of_generic (r + 1) ↥Y _ _ σ hGen
  let T : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
      →ₗ[ℂ] (Y →ₗ[ℂ] Automorphic.realStandardKFinite (r + 1) ds) :=
    LinearMap.lcomp ℂ (Automorphic.realStandardKFinite (r + 1) ds) Y.subtype ∘ₗ
      (envelopingAction π).toLinearMap
  have hCentral (u) (hu : T u = 0) : u ∈ realStandardCentralIdeal (r + 1) ds := by
    have hVan (w : Y) : envelopingAction π u w.val = 0 := by
      change T u w = 0
      rw [hu, LinearMap.zero_apply]
    exact mem_centralIdeal_of_vanishes_on_subspace π Y hY.2
      (realStandardLie_hasInfinitesimalCharacter (r + 1) ds) hFaithful hv hv₀ u hVan
  obtain ⟨c, hc, hLower⟩ := realStandardCentralGrowth (r + 1) ds ⟨v, hv₀⟩
  obtain ⟨C, hUpper⟩ := realLeftPolynomialGrowth (r + 1) ds p k hp Y hPol
  have hn : 1 ≤ (r + 1) * ((r + 1) - 1) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  exact RealLinkedQuotientGrowth.not_forall_le hc hn
    (fun d => hLower d T (fun u _ hu => hCentral u hu)) hUpper (fun _ => le_rfl)

end Langlands.Global.RankinSelbergGlobal.RealLocalWhittaker
