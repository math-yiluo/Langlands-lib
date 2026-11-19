import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealSphericalInduction
import Langlands.Representation.Archimedean.RealSphericalCyclic
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-!
# Proof of the spherical cyclicity in the closed Langlands chamber

We prove `RealSphericalCyclicStatement`. For a list of parity-zero real characters, the real
standard module is the principal series of the position characters, which are signed powers
with trivial signs and exponents with weakly decreasing real parts. Given a Lie-stable `W`
containing a nonzero `O(n)`-fixed `T`, the largest `O(n)`-stable subspace `W'` of `W` is still
Lie-stable and contains `T`. Its annihilator in the dual principal series is `O(n)`-stable,
Lie-stable and orthogonal to `T`, which is a nonzero constant on `O(n)`; by
`RealSphericalInduction.eq_bot` it is zero. Hence `W'`, and so `W`, is everything.
-/

noncomputable section

open MeasureTheory Matrix

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealSphericalCyclicProof

open MaximalParabolicIntegration PartialJacquet JacquetDual GramFormula Langlands.GeneralLinear RealSphericalChart
  Langlands.LocalFactor.Archimedean RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_rscp (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-! ## Lists of characters -/

theorem realStandardModule_map_character (n : ℕ) (ds : List RealCharacterData) :
    realStandardModule n (ds.map RealBlock.character) =
      principalSeries ℝ n (realPositionCharacter (ds.map RealBlock.character)) := by
  ext f
  constructor
  · exact fun hf => hf.1
  · intro hf
    refine ⟨hf, fun p d hd => ?_⟩
    rw [RealPrincipalSeriesDuality.realInducedBlockAt_map_character ds p] at hd
    cases hd

theorem realPositionCharacter_map_one : ∀ (ds : List RealCharacterData) (l : ℕ),
    realPositionCharacter (ds.map RealBlock.character) l 1 = 1
  | [], _ => rfl
  | _ :: _, 0 => by simp [realPositionCharacter]
  | _ :: ds, l + 1 => by
      simp only [List.map_cons, realPositionCharacter]
      exact realPositionCharacter_map_one ds l

theorem realPositionCharacter_map_neg_one : ∀ (ds : List RealCharacterData),
    (∀ d ∈ ds, d.parity = 0) →
      ∀ l : ℕ, realPositionCharacter (ds.map RealBlock.character) l (-1) = 1
  | [], _, _ => rfl
  | d :: _, h, 0 => by
      simp only [List.map_cons, realPositionCharacter]
      rw [d.character_eq, h d List.mem_cons_self]
      simp
  | _ :: ds, h, l + 1 => by
      simp only [List.map_cons, realPositionCharacter]
      exact realPositionCharacter_map_neg_one ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) l

theorem isSignedPower_map (ds : List RealCharacterData) (h : ∀ d ∈ ds, d.parity = 0) :
    IsSignedPower (realPositionCharacter (ds.map RealBlock.character))
      (realPositionExponent (ds.map RealBlock.character)) where
  eq := realPositionCharacter_eq_signUnit_mul _
  one := realPositionCharacter_map_one ds
  norm_neg_one l := by rw [realPositionCharacter_map_neg_one ds h l, norm_one]

theorem isWeaklyDominant_map : ∀ (ds : List RealCharacterData),
    IsRealLanglandsOrdered (ds.map RealBlock.character) →
      IsWeaklyDominant (realPositionExponent (ds.map RealBlock.character)) (ds.length - 1)
  | [], _ => fun l hl => by simp at hl
  | d :: ds, h => by
      unfold IsRealLanglandsOrdered at h
      rw [List.map_cons, List.pairwise_cons] at h
      have ih := isWeaklyDominant_map ds h.2
      intro l hl
      have hl' : l < ds.length := by simpa using hl
      cases l with
      | zero =>
          cases ds with
          | nil => simp at hl'
          | cons d' ds'' =>
              have hrel := h.1 (RealBlock.character d') (by simp)
              simpa [realPositionExponent, realBlockExponent] using hrel
      | succ l =>
          simp only [List.map_cons, realPositionExponent]
          exact ih l (by omega)

/-! ## The proof -/

theorem unitary_toUnits_mk {n : ℕ} {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) :
    Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ : Matrix.unitaryGroup (Fin n) ℝ) = k :=
  Units.ext rfl

/-- **Spherical cyclicity in the closed Langlands chamber.** -/
theorem realSphericalCyclic : RealSphericalCyclicStatement := by
  intro n ds hlen hpar hord T hTK hT0 W hTW hWL
  set χ := realPositionCharacter (ds.map RealBlock.character) with hχdef
  set e := realPositionExponent (ds.map RealBlock.character) with hedef
  have hχ : IsSignedPower χ e := isSignedPower_map ds hpar
  have hp : ∀ l, χ l (-1) = 1 := realPositionCharacter_map_neg_one ds hpar
  have he : IsWeaklyDominant e (n - 1) := by
    rw [← hlen]
    exact isWeaklyDominant_map ds hord
  have hKF : kFiniteFunctions (realStandardModule n (ds.map RealBlock.character)) (unitaryCompact ℝ n) =
      kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
    rw [realStandardModule_map_character]
  -- the largest `O(n)`-stable subspace of `W`
  set W' : Submodule ℂ (RealTemperedCommutantReduction.KF n (ds.map RealBlock.character)) :=
    ⨅ k, W.comap (realStandardRep n (ds.map RealBlock.character) k) with hW'def
  have hmemW' : ∀ w, w ∈ W' ↔ ∀ k, realStandardRep n (ds.map RealBlock.character) k w ∈ W := fun w => by
    simp only [hW'def, Submodule.mem_iInf, Submodule.mem_comap]
  have hW'K : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) w, w ∈ W' →
      realStandardRep n (ds.map RealBlock.character) k w ∈ W' := by
    intro k w hw
    rw [hmemW'] at hw ⊢
    intro k'
    rw [← Module.End.mul_apply, ← map_mul]
    exact hw (k' * k)
  have hW'D : ∀ (X : Matrix (Fin n) (Fin n) ℝ) w, w ∈ W' →
      realStandardLie n (ds.map RealBlock.character) (1 ⊗ₜ X) w ∈ W' := by
    intro X w hw
    rw [hmemW'] at hw ⊢
    intro k
    have hcomm : realStandardRep n (ds.map RealBlock.character) k (realStandardLie n (ds.map RealBlock.character) (1 ⊗ₜ X) w) =
        realStandardLie n (ds.map RealBlock.character)
          (1 ⊗ₜ (((Unitary.toUnits k : Langlands.GeneralLinear n ℝ) :
              Matrix (Fin n) (Fin n) ℝ) * X *
            (((Unitary.toUnits k)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)))
          (realStandardRep n (ds.map RealBlock.character) k w) := by
      apply Subtype.ext
      simp only [realStandardRep_apply_coe, realStandardLie_one_tmul_apply_coe]
      exact rightTranslation_rightDerivative w.2.1.1.1 X _
    rw [hcomm]
    exact hWL _ _ (hw k)
  -- the corresponding space of functions
  set V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
    W'.map (kFiniteFunctions (realStandardModule n (ds.map RealBlock.character)) (unitaryCompact ℝ n)).subtype with hVdef
  have hV : V ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
    rintro _ ⟨w, _, rfl⟩
    rw [← hKF]
    exact w.2
  have hVK : ∀ k ∈ unitaryCompact ℝ n, ∀ f ∈ V,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f ∈ V := by
    rintro k hk _ ⟨w, hw, rfl⟩
    refine ⟨realStandardRep n (ds.map RealBlock.character) ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w, hW'K _ w hw, ?_⟩
    simp only [Submodule.coe_subtype, realStandardRep_apply_coe, unitary_toUnits_mk hk]
  have hVD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ V,
      rightDerivative (matrixModel ℝ n) X f ∈ V := by
    rintro X _ ⟨w, hw, rfl⟩
    refine ⟨realStandardLie n (ds.map RealBlock.character) (1 ⊗ₜ X) w, hW'D X w hw, ?_⟩
    simp only [Submodule.coe_subtype, realStandardLie_one_tmul_apply_coe]
  -- the fixed vector
  have hT1 : ∀ k ∈ unitaryCompact ℝ n,
      (T : Langlands.GeneralLinear n ℝ → ℂ) k = (T : Langlands.GeneralLinear n ℝ → ℂ) 1 := by
    intro k hk
    have h1 := congrArg (fun f : RealTemperedCommutantReduction.KF n (ds.map RealBlock.character) =>
      (f : Langlands.GeneralLinear n ℝ → ℂ) 1) (hTK ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩)
    simp only [realStandardRep_apply_coe, unitary_toUnits_mk hk] at h1
    change (T : Langlands.GeneralLinear n ℝ → ℂ) (1 * k) = _ at h1
    rwa [one_mul] at h1
  have hT1ne : (T : Langlands.GeneralLinear n ℝ → ℂ) 1 ≠ 0 := by
    intro h0
    apply hT0
    apply Subtype.ext
    funext g
    obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
    have hmem : (T : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n χ := T.2.1.1
    rw [hmem.2 a u k, hT1 k hk, h0, mul_zero]
    simp
  have hTV : (T : Langlands.GeneralLinear n ℝ → ℂ) ∈ V :=
    ⟨T, (hmemW' T).2 fun k => by rw [hTK k]; exact hTW, rfl⟩
  -- the annihilator
  set A := JacquetKernel.annihilator χ V hV with hAdef
  have hAK := JacquetKernel.annihilator_rightTranslation V hV hVK
  have hAD := JacquetKernel.annihilator_rightDerivative hχ V hV hVD
  have hAint : ∀ u ∈ A, ∫ k, u (k : Langlands.GeneralLinear n ℝ) ∂haarK n = 0 := by
    intro u hu
    have h1 := hu.2 _ hTV
    have h2 : ∫ k, u (k : Langlands.GeneralLinear n ℝ) *
        (T : Langlands.GeneralLinear n ℝ → ℂ) k ∂haarK n =
          (∫ k, u (k : Langlands.GeneralLinear n ℝ) ∂haarK n) *
            (T : Langlands.GeneralLinear n ℝ → ℂ) 1 := by
      rw [← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun k => by
        simp only
        rw [hT1 _ k.2])
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_right hT1ne
  have hAbot : A = ⊥ := RealSphericalInduction.eq_bot n hχ hp he
    (JacquetKernel.annihilator_le (χ := χ) V hV) hAK hAD hAint
  -- every function lies in `V`
  rw [eq_top_iff]
  intro w _
  have hwV : (w : Langlands.GeneralLinear n ℝ → ℂ) ∈ V := by
    by_contra hwV
    have hw : (w : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
      rw [← hKF]
      exact w.2
    exact JacquetKernel.annihilator_ne_bot hχ V hV hVK hw hwV hAbot
  obtain ⟨w', hw', hww'⟩ := hwV
  have hww : w' = w := Subtype.ext hww'
  rw [← hww]
  have h1 := (hmemW' w').1 hw' 1
  rwa [map_one, Module.End.one_apply] at h1

end RealSphericalCyclicProof

end Langlands.Archimedean
