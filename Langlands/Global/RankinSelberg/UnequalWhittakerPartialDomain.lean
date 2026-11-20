import Langlands.Global.RankinSelberg.FiniteWhittakerSemilocalProduct
import Langlands.Global.RankinSelberg.UnequalKernelLocalPoint

/-! # Removing the away coordinates of ordinary unequal-rank Whittaker tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.RankinSelbergGlobal.FiniteWhittakerSemilocal

open NumberField Automorphic FiniteAdelicGL FiniteWhittakerPartialDomain
open LocalPointFactorization UnipotentClass

variable {F : Type u} [Field F] [NumberField F]

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : DecidableEq (FinitePlace F) := Classical.decEq _

private theorem pad_finiteInclusion {m n : ℕ} (hle : m ≤ n) (d : FiniteAdelicGL F m) :
    pad F hle ((GeneralLinearGroupPoints.adelicEquiv F m).symm (AdelicGL.ofFinite F m d)) =
      (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofFinite F n (padGL hle d)) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [UnequalAnalytic.adelicEquiv_pad, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  apply adelicGL_ext_infinite_finite
  · rw [infinite_padGL, infinite_ofFinite F, infinite_ofFinite F, map_one]
  · rw [finite_padGL, finite_ofFinite F, finite_ofFinite F]

variable [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {S : Finset (FinitePlace F)}

/-- The padded product depends only on the retained coordinates of a point of the
partial domain. -/
def UnequalPairDependsOnRetained (hrt : t < r) (S : Finset (FinitePlace F))
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) : Prop :=
  let hle := Nat.le_of_lt (Nat.succ_lt_succ hrt)
  ∀ g ∈ unipotentIntegralOutside F (t + 1) S,
    W (pad F hle g) * W' g = W (pad F hle (retainedPoint S g)) * W' (retainedPoint S g)

/-- On a partial unequal-rank class, the paired Whittaker product of prescribed tensor
vectors depends only on the retained coordinates of the small matrix. -/
theorem unequal_whittaker_pair_eq_retained (hrt : t < r)
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (b : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (b' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u)) :
    let W := cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] b))
    let W' := cuspWhittaker F T' ψ⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] b'))
    UnequalPairDependsOnRetained hrt S W W' := by
  dsimp only [UnequalPairDependsOnRetained]
  intro g hg
  let hle := Nat.le_of_lt (Nat.succ_lt_succ hrt)
  let x := P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] b)
  let x' := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] b')
  let W := cuspWhittaker F T ψ x
  let W' := cuspWhittaker F T' ψ⁻¹ x'
  let gS := retainedPoint S g
  change W (pad F hle g) * W' g = W (pad F hle gS) * W' gS
  obtain ⟨n, hn, k, hk, hsplit⟩ := exists_unipotent_mul_mul_of_mem_unipotentIntegralOutside F (t + 1) S hg
  let u : unipotentAdelic F (t + 1) := ⟨n, hn⟩
  let away : awayIntegralSubgroup F (t + 1) S := ⟨k, hk⟩
  let d := awayFinite S away
  let dBig := padGL hle d
  let point := (GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (AdelicGL.ofFinite F (t + 1) d)
  let pointBig := (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
    (AdelicGL.ofFinite F (r + 1) dBig)
  have hsplit' : g = u.val * (gS * point) := by
    rw [mul_assoc, adelicSplit_away S away] at hsplit
    exact hsplit
  have hpad : pad F hle g = (Unfolding.padUnipotent F hle u).val *
      (pad F hle gS * pointBig) := by
    rw [hsplit', Unfolding.pad_mul, Unfolding.pad_mul, pad_finiteInclusion]
    rfl
  have hBigS (v : S) : localProjection F (r + 1) v dBig = 1 := by
    change localProjection F (r + 1) v (padGL hle (awayFinite S away)) = 1
    rw [localProjection_padGL, awayFinite_at_S S away, map_one]
  have hBigA (v : FinitePlace F) (hv : v ∉ S) :
      localProjection F (r + 1) v dBig ∈ localIntegral F (r + 1) v := by
    change localProjection F (r + 1) v (padGL hle (awayFinite S away)) ∈ _
    rw [localProjection_padGL]
    exact padGL_mem_localIntegral hle (awayFinite_integral S away v hv)
  have hwBig : W (pad F hle gS * pointBig) = W (pad F hle gS) := by
    change cuspWhittaker F T ψ x (pad F hle gS * pointBig) = _
    rw [← UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F ψ T dBig,
      fullVector_fixed_away P hP S hPS a b dBig hBigS hBigA]
  have hwSmall : W' (gS * point) = W' gS := by
    simpa only [adelicSplit_away S away] using
      whittaker_mul_away P' hP' S hPS' ψ⁻¹ a' b' gS away
  have hχ : genericCharacter F t ψ (fun _ => 1) u ≠ 0 := by
    intro hz
    have hn' := Unfolding.norm_genericCharacter F t ψ hψ.2.2.2 (fun _ => 1) u
    rw [hz, norm_zero] at hn'
    exact zero_ne_one hn'
  calc
    _ = (genericCharacter F t ψ (fun _ => 1) u * W (pad F hle gS)) *
        ((genericCharacter F t ψ (fun _ => 1) u)⁻¹ * W' gS) := by
      conv_lhs =>
        congr
        · rw [hpad]
        · rw [hsplit']
      change cuspWhittaker F T ψ x _ * cuspWhittaker F T' ψ⁻¹ x' _ = _
      rw [Unfolding.cuspWhittaker_mul_left F T ψ hψ,
        Unfolding.cuspWhittaker_mul_left F T' ψ⁻¹ (Unfolding.isStandardAdditiveCharacter_inv F ψ hψ),
        Unfolding.genericCharacter_padUnipotent, UnramifiedWhittaker.genericCharacter_inv]
      change (_ * W (pad F hle gS * pointBig)) * (_ * W' (gS * point)) = _
      rw [hwBig, hwSmall]
    _ = _ := by
      rw [mul_mul_mul_comm, mul_inv_cancel₀ hχ, one_mul]

end Langlands.Global.RankinSelbergGlobal.FiniteWhittakerSemilocal
