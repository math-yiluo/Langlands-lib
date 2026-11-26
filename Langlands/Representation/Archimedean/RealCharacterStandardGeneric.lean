import Langlands.Global.RankinSelberg.RealGodementCanonicalNonzero
import Langlands.Global.RankinSelberg.RealEqualDualConvergence
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.GKModule

/-! # Real character standard modules are generic -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory
open scoped Matrix.Norms.Operator Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealGodementProfiles RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- At every exponent vector some K-finite real character section has a canonical Jacquet
coefficient that does not vanish at the long Weyl element. -/
theorem exists_canonicalJacquetMap_weylLong_ne_zero (r : ℕ) (a : ℝˣ)
    (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ) :
    ∃ f : Automorphic.realStandardKFinite (r + 1) (characterList p z),
      canonicalJacquetMap a p z f (weylLong (r + 1) ℝ) ≠ 0 := by
  cases r with
  | zero =>
    let d := charData (p 0) (z 0)
    have hList : characterList p z = [.character d] := by
      simp only [characterList, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, d]
    let f : Automorphic.realStandardKFinite 1 (characterList p z) :=
      ⟨RealRankOneStandardModule.characterVector d,
        hList.symm ▸ RealRankOneStandardModule.characterVector_mem d⟩
    refine ⟨f, ?_⟩
    have hz : z ∈ realSpectralChamber 0 := fun i => Fin.elim0 i
    have hw : weylLong 1 ℝ = (1 : Langlands.GeneralLinear 1 ℝ) := by
      apply Units.ext
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [canonicalJacquetMap_agrees a p hz f, hw]
    intro he
    rw [additiveJacquetIntegral_rankOne] at he
    change RealRankOneStandardModule.characterVector d 1 = 0 at he
    exact one_ne_zero ((RealRankOneStandardModule.characterVector_one d).symm.trans he)
  | succ t =>
    let p' (i : Fin (t + 1)) := p i.succ
    let z' (i : Fin (t + 1)) := z i.succ
    obtain ⟨f, hf⟩ := realGodementCanonicalNonzero t a p' z'
    let W := canonicalJacquetMap a p' z' f
    let D := (nonempty_realQuotientMeasureData t a).some
    let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
    have hGrowth := RealUniformWhittaker.uniformDerivativeGrowth_of_mem_model
      (canonicalJacquetMap_mem_uniformModel a p' z' f)
    obtain ⟨S, hS, hRank, Φ, hSupport, hFinite, hNZ⟩ := realGodementPolynomialTest D a W
      (canonicalJacquetMap_derivative_mem_regularFunctions a p' z' f) hGrowth hf (p 0) (z 0)
    let φ := compactRestriction f.val
    have hφ : IsCompactProfile p' φ := isCompactProfile_compactRestriction f.property
    obtain ⟨E, hE, hConv, C, hLower, hTest⟩ :=
      realGodementFiniteCompactTest D.groupHaar p φ hφ S hS hRank Φ hSupport hFinite
    let := hE
    have hLowerEval : canonicalJacquetFamily a C.lower_profile z' = W := by
      rw [← canonicalJacquetMap_standardSection a C.lower_profile z']
      apply congrArg (canonicalJacquetMap a p' z')
      apply Subtype.ext
      change standardSection z' C.lower = f.val
      rw [hLower]
      exact standardSection_compactRestriction f.property
    let f' := spectralFrameKFiniteLift p E hConv z (C.frameVector D hConv z)
    refine ⟨f', fun hv => hNZ ?_⟩
    change canonicalJacquetMap a p z f' (weylLong (t + 2) ℝ) = 0 at hv
    rw [show f' = spectralFrameKFiniteLift p E hConv z (C.frameVector D hConv z) from rfl,
      realGodementCanonicalColumn D a p E hConv, hTest,
      show (fun i => z i.succ) = z' from rfl, hLowerEval] at hv
    exact hv

end Langlands.Global.RankinSelbergGlobal.RealGodement

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Global.RankinSelbergGlobal

namespace RealCharacterStandardGeneric

/-- The superdiagonal sum of `1 + t X` is `t` times that of `X`. -/
private theorem superdiag_one_add_smul {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (t : ℝ) :
    ∑ i : Fin r, (1 + t • X) i.castSucc i.succ = t * ∑ i : Fin r, X i.castSucc i.succ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : (i.castSucc : Fin (r + 1)) ≠ i.succ := Fin.castSucc_lt_succ.ne
  simp [Matrix.one_apply_ne hne]

/-- The derivative at the identity, in a strictly upper triangular direction, of a smooth
function transforming on the left under the upper unipotent group by the Whittaker
character. -/
theorem rightDerivative_one_of_whittaker {r : ℕ} {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (hcov : ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ,
      ∀ g, W (u * g) = realWhittakerCharacter a u * W g)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (hX : ∀ i j : Fin (r + 1), (j : ℕ) ≤ i → X i j = 0) :
    rightDerivative (matrixModel ℝ (r + 1)) X W 1 =
      ((2 * Real.pi * ((a : ℝ) * ∑ i : Fin r, X i.castSucc i.succ) : ℝ) * Complex.I) *
        W 1 := by
  have hU : X.IsUpperTriangular := fun i j hij => hX i j (le_of_lt hij)
  have hd : ∀ i, X i i = 0 := fun i => hX i i le_rfl
  set s : ℝ := ∑ i : Fin r, X i.castSucc i.succ with hs
  rw [rightDerivative_eq_fderiv_mul_left hW X 1]
  set F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ := fun y =>
    unitsExtension W (((1 : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1))
      (Fin (r + 1)) ℝ) * y) with hF
  have hFd : DifferentiableAt ℝ F 1 := differentiableAt_unitsExtension_mul_left hW 1
  have hγ : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) + t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
  have hγ0 : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) + (0 : ℝ) • X = 1 := by simp
  have h1 : HasDerivAt (fun t : ℝ => F (1 + t • X)) (fderiv ℝ F 1 X) 0 := by
    have h' : HasFDerivAt F (fderiv ℝ F 1)
        ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) + (0 : ℝ) • X) := by
      rw [hγ0]
      exact hFd.hasFDerivAt
    exact h'.comp_hasDerivAt (0 : ℝ) hγ
  have hval : (fun t : ℝ => F (1 + t • X)) =
      fun t => Complex.exp (((2 * Real.pi * ((a : ℝ) * (t * s)) : ℝ) : ℂ) * Complex.I) * W 1 := by
    funext t
    let u := RealPrincipalSeriesDuality.unipotentLine X hU hd t
    have hu : ((u : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
        1 + t • X := RealPrincipalSeriesDuality.unipotentLine_val X hU hd t
    have hF1 : F (1 + t • X) = W (u : Langlands.GeneralLinear (r + 1) ℝ) := by
      simp only [hF, Units.val_one, Matrix.one_mul, ← hu, unitsExtension_val]
    rw [hF1]
    have hc := hcov u u.2 1
    rw [mul_one] at hc
    rw [hc, realWhittakerCharacter,
      Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      realScaledCharacter_apply, Real.fourierChar_apply]
    congr 4
    rw [hu, superdiag_one_add_smul]
  have h2 : HasDerivAt (fun t : ℝ =>
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (t * s)) : ℝ) : ℂ) * Complex.I) * W 1)
      (((2 * Real.pi * ((a : ℝ) * s) : ℝ) * Complex.I) * W 1) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => (((2 * Real.pi * ((a : ℝ) * (t * s)) : ℝ) : ℂ) *
        Complex.I)) (((2 * Real.pi * ((a : ℝ) * s) : ℝ) : ℂ) * Complex.I) 0 := by
      have hr : HasDerivAt (fun t : ℝ => (2 * Real.pi * ((a : ℝ) * (t * s)) : ℝ))
          (2 * Real.pi * ((a : ℝ) * s)) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).mul_const s).const_mul ((a : ℝ))
        have := this.const_mul (2 * Real.pi)
        simpa using this
      exact (hr.ofReal_comp).mul_const Complex.I
    have := (Complex.hasDerivAt_exp _).comp (0 : ℝ) hlin
    have := this.mul_const (W 1)
    simpa using this
  rw [hval] at h1
  exact h1.unique h2

/-- The superdiagonal sum in the form of `IsRealGenericGKModule`. -/
private theorem sum_superdiag_eq {r : ℕ} (c : ℝ) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
    (∑ i : Fin (r + 1), ∑ j : Fin (r + 1), if (j : ℕ) = i + 1 then c * X i j else 0) =
      c * ∑ i : Fin r, X i.castSucc i.succ := by
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  have hlast : (∑ j : Fin (r + 1), if (j : ℕ) = (Fin.last r : ℕ) + 1 then c * X (Fin.last r) j
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (j : ℕ) ≠ (Fin.last r : ℕ) + 1 := by
      have := j.2
      simp only [Fin.val_last]
      omega
    simp only [this, ↓reduceIte]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    have : (j : ℕ) ≠ (i.castSucc : ℕ) + 1 := by
      intro h
      apply hj
      ext
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
      omega
    simp only [this, ↓reduceIte]
  · simp

end RealCharacterStandardGeneric

open RealCharacterStandardGeneric Langlands.Global.RankinSelbergGlobal.RealGodement
  Langlands.Global.RankinSelbergGlobal.RealGodementProfiles in
/-- The `O(n)`-finite standard module of a list of real characters of positive rank is
generic: evaluation at the identity of the canonical continued Jacquet coefficient is a
nonzero Whittaker functional. -/
theorem isRealGeneric_characterList (r : ℕ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ) :
    IsRealGenericGKModule (r + 1) (realStandardLie (r + 1) (characterList p z)) := by
  let a : ℝˣ := 1
  let B := canonicalJacquetMap a p z
  have hB : IsRealWhittakerIntertwiner r (characterList p z) (-a) B :=
    (realGodementCanonicalModel r a p z).1
  let ℓ : kFiniteFunctions (realStandardModule (r + 1) (characterList p z))
      (unitaryCompact ℝ (r + 1)) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear (r + 1) ℝ => ℂ) 1).comp B
  refine ⟨ℓ, ?_, fun _ => -(2 * Real.pi), fun _ _ => by
    simp [Real.pi_pos.ne'], fun X hX v => ?_⟩
  · obtain ⟨f, hf⟩ := exists_canonicalJacquetMap_weylLong_ne_zero r a p z
    let w : unitaryCompact ℝ (r + 1) :=
      ⟨weylLong (r + 1) ℝ, RealEqualDualConvergence.weylLong_mem_unitary⟩
    let k : Matrix.unitaryGroup (Fin (r + 1)) ℝ :=
      ⟨((weylLong (r + 1) ℝ : Langlands.GeneralLinear (r + 1) ℝ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ), RealEqualDualConvergence.weylLong_mem_unitary⟩
    let f' := realStandardRep (r + 1) (characterList p z) k f
    have hf' : (f' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) =
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)
          (w : Langlands.GeneralLinear (r + 1) ℝ) f := by
      have hkw : (Unitary.toUnits k : Langlands.GeneralLinear (r + 1) ℝ) =
          (w : Langlands.GeneralLinear (r + 1) ℝ) := Units.ext rfl
      rw [realStandardRep_apply_coe, hkw]
    have hBf := hB.2.2.2.1 w f f' hf'
    intro h0
    apply hf
    have h1 := LinearMap.congr_fun h0 f'
    change B f' 1 = 0 at h1
    rw [hBf] at h1
    change B f (1 * (weylLong (r + 1) ℝ : Langlands.GeneralLinear (r + 1) ℝ)) = 0 at h1
    rwa [one_mul] at h1
  · let v' := realStandardLie (r + 1) (characterList p z) (1 ⊗ₜ X) v
    have hv' : (v' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) =
        rightDerivative (matrixModel ℝ (r + 1)) X v := kFiniteLie_one_tmul_apply_coe _ _ _ _ X v
    have hBv := hB.2.2.2.2 X v v' hv'
    change B v' 1 = _ * B v 1
    rw [hBv, rightDerivative_one_of_whittaker (hB.2.1 v) (hB.1 v) X hX, sum_superdiag_eq]
    have ha : ((a : ℝˣ) : ℝ) = 1 := rfl
    congr 1
    simp only [Units.val_neg, ha]
    push_cast
    ring

end Langlands.Archimedean
