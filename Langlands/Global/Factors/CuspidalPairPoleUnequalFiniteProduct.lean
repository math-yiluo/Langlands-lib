import Langlands.Global.Factors.CuspidalPairPoleFiniteTestVectors
import Langlands.Global.RankinSelberg.UnequalWhittakerPartialDomain

/-! # Prescribed finite factorization of the ordinary unequal-rank Whittaker product -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ

open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open NumberField Automorphic CompletionPadic
open RankinSelbergGlobal RankinSelbergGlobal.UnipotentClass
open FiniteWhittakerTensor FiniteWhittakerSemilocal
open RankinSelbergGlobal.FiniteWhittakerPartialDomain
open LocalPointFactorization FiniteAdelicGL
open Langlands.ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

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

private theorem pad_retainedPoint_eq {r t : ℕ} (hle : t + 1 ≤ r + 1)
    (S : Finset (FinitePlace F)) (g : Points F (t + 1)) :
    pad F hle (retainedPoint S g) = pad F hle (infinitePoint S g) *
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) (padGL hle (localFinite S g))) := by
  rw [retainedPoint_eq, Unfolding.pad_mul]
  congr 1
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [UnequalAnalytic.adelicEquiv_pad, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  apply AdelicGL.ext_infinite_finite F (r + 1)
  · rw [infinite_padGL, infinite_ofFinite F, infinite_ofFinite F, map_one]
  · rw [finite_padGL, finite_ofFinite F, finite_ofFinite F]

variable [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {S : Finset (FinitePlace F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

/-- The ordinary unequal-rank product factors across the specified finite components.
`U` and `U'` are the two Whittaker functions at the reference finite vectors. -/
def HasOrdinaryUnequalFiniteProduct (hrt : t < r)
    (D : ∀ v : S, PoleFiniteTestVectors v.1 (ψv v) P P')
    (W U : Points F (r + 1) → ℂ) (W' U' : Points F (t + 1) → ℂ) : Prop :=
  let hle := Nat.le_of_lt (Nat.succ_lt_succ hrt)
  ∀ g ∈ unipotentIntegralOutside F (t + 1) S,
    W (pad F hle g) * W' g =
      (U (pad F hle (infinitePoint S g)) * U' (infinitePoint S g)) *
        ∏ v : S, (D v).left.val (padGL hle (finiteComponent F (t + 1) v g)) *
          (D v).right.val (finiteComponent F (t + 1) v g)

/-- Prescribed coefficient functions on both sets of finite tensor factors give the finite
product identity for arbitrary choices of their infinite tensors. -/
theorem hasOrdinaryUnequalFiniteProduct (hrt : t < r)
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (D : ∀ v : S, PoleFiniteTestVectors v.1 (ψv v) P P')
    (b : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (b' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u)) :
    let a (v : S) := (D v).leftFactor.vector
    let a' (v : S) := (D v).rightFactor.vector
    let a₀ (v : S) := (D v).leftFactor.reference
    let a₀' (v : S) := (D v).rightFactor.reference
    let W := cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] b))
    let W' := cuspWhittaker F T' ψ.complex⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] b'))
    let U := cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] b))
    let U' := cuspWhittaker F T' ψ.complex⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a₀' ⊗ₜ[ℂ] b'))
    HasOrdinaryUnequalFiniteProduct hrt D W U W' U' := by
  intro a a' a₀ a₀' W W' U U'
  dsimp only [HasOrdinaryUnequalFiniteProduct]
  intro g hg
  let hle := Nat.le_of_lt (Nat.succ_lt_succ hrt)
  let ℓ (v : S) := (D v).leftFactor.functional
  let ℓ' (v : S) := (D v).rightFactor.functional
  let d := padGL hle (localFinite S g)
  let gInf := pad F hle (infinitePoint S g)
  have hgInf (v : S) : finiteComponent F (r + 1) v gInf = 1 := by
    change finiteComponent F (r + 1) v (pad F hle (infinitePoint S g)) = 1
    rw [finiteComponent_pad, infinitePoint_finite, map_one]
  have hd (v : FinitePlace F) (hv : v ∉ S) : localProjection F (r + 1) v d ∈ localIntegral F (r + 1) v := by
    change localProjection F (r + 1) v (padGL hle (localFinite S g)) ∈ _
    rw [localProjection_padGL, localFinite_away S g v hv, map_one]
    exact (localIntegral F (r + 1) v).one_mem
  have hL := translated_coefficient_eq_product P hP S hPS ψ hψF ψv hψv ℓ a₀
    (fun v => (D v).leftFactor.reference_value) gInf hgInf d hd b a
  have hLeft : W (pad F hle (retainedPoint S g)) =
      (∏ v : S, (D v).left.val (padGL hle (finiteComponent F (t + 1) v g))) * U gInf := by
    refine (congrArg W (pad_retainedPoint_eq hle S g)).trans (hL.trans ?_)
    exact congrArg (fun p : ℂ => p * U gInf) <| Finset.prod_congr rfl fun v _ => by
      have hv : localProjection F (r + 1) v d = padGL hle (finiteComponent F (t + 1) v g) := by
        change localProjection F (r + 1) v (padGL hle (localFinite S g)) = _
        rw [localProjection_padGL, localFinite_at_S S g v]
      rw [hv]
      exact (D v).leftFactor.coefficient_eq _
  have hinvF : ∀ x : F, inverseCharacter ψ (algebraMap F (Adeles F) x) = 1 := by
    intro x
    rw [inverseCharacter_apply, hψF, inv_one]
  have hR := coefficient_eq_product_at_retained S P' hP' hPS' (inverseCharacter ψ) hinvF
    (fun v => inverseFinite v.1 (ψv v)) (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v))
    ℓ' a₀' (fun v => (D v).rightFactor.reference_value) a' b' g
  simp only [complex_inverseCharacter] at hR
  have hRight : W' (retainedPoint S g) =
      (∏ v : S, (D v).right.val (finiteComponent F (t + 1) v g)) * U' (infinitePoint S g) :=
    hR.trans (congrArg (fun p : ℂ => p * U' (infinitePoint S g)) <|
      Finset.prod_congr rfl fun v _ => (D v).rightFactor.coefficient_eq _)
  have hψ := isStandardAdditiveCharacter_of_unitary ψ hψF
  have hpair : W (pad F hle g) * W' g =
      W (pad F hle (retainedPoint S g)) * W' (retainedPoint S g) :=
    unequal_whittaker_pair_eq_retained (P := P) (P' := P') hrt hP hP' hPS hPS' ψ.complex hψ a a' b b' g hg
  refine hpair.trans ((congrArg₂ (· * ·) hLeft hRight).trans ?_)
  exact (mul_mul_mul_comm _ _ _ _).trans ((mul_comm _ _).trans
    (congrArg (fun z : ℂ => (U gInf * U' (infinitePoint S g)) * z) (Finset.prod_mul_distrib ..).symm))

end Langlands.Global.CuspidalPairPoles
