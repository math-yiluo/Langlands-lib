import Langlands.Automorphic.CuspidalPresentationTensorDecomposition
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.UnipotentClassDecomposition

/-! # Removing the finite coordinates outside S from paired Whittaker products -/

noncomputable section
open scoped TensorProduct Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.FiniteWhittakerPartialDomain

open Langlands.Automorphic Langlands.Global.FiniteAdelicGL UnipotentClass

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance partialDomainSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance partialDomainSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance partialDomainRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance partialDomainContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance partialDomainSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance partialDomainFormsGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance partialDomainStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance partialDomainSpaceGroup (A : CuspidalOperatorRealization F r) : AddCommGroup A.Space :=
  Submodule.addCommGroup _
local instance partialDomainDecEq : DecidableEq (FinitePlace F) := Classical.decEq _

variable (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
  (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)

/-- The actual finite pure vector is fixed by the combined integral action away from S. -/
theorem finitePure_fixed_away
    (a : ∀ v : S, P.localFactor v) (d : FiniteAdelicGL F (r + 1))
    (hdS : ∀ v : S, localProjection F (r + 1) v d = 1)
    (hdA : ∀ v ∉ S, localProjection F (r + 1) v d ∈ localIntegral F (r + 1) v) :
    P.finiteTensorRepresentation d (P.finitePure S hPS a) = P.finitePure S hPS a := by
  have h := tensorRepresentation_pure_of_mem F (r + 1)
    (fun v => (P.localFactor v).representation) P.tensorExceptional P.reference P.reference_fixed
    d ⟨S, P.unramified.exceptional_subset.trans hPS⟩ hdA a
  have hlocal : (fun v : S => (P.localFactor v).representation
      (localProjection F (r + 1) v d) (a v)) = a := by
    funext v
    rw [hdS, map_one, Module.End.one_apply]
  exact h.trans (congrArg (Langlands.RestrictedTensor.pure P.tensorExceptional P.reference
    ⟨S, P.unramified.exceptional_subset.trans hPS⟩) hlocal)

/-- The actual global tensor vector is fixed by integral finite translations trivial on S. -/
theorem fullVector_fixed_away
    (a : ∀ v : S, P.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (d : FiniteAdelicGL F (r + 1))
    (hdS : ∀ v : S, localProjection F (r + 1) v d = 1)
    (hdA : ∀ v ∉ S, localProjection F (r + 1) v d ∈ localIntegral F (r + 1) v) :
    T.realization.finiteRepresentation d
      (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) =
        P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t) :=
  (P.allPlaceTensorEquiv_finite hP d (P.finitePure S hPS a) t).symm.trans
    (congrArg (fun z => P.allPlaceTensorEquiv hP (z ⊗ₜ[ℂ] t))
      (finitePure_fixed_away P S hPS a d hdS hdA))

/-- A finite adelic matrix supported away from S with integral components. -/
def awayFinite (k : awayIntegralSubgroup F (r + 1) S) : FiniteAdelicGL F (r + 1) :=
  (splitAtPlaces F (r + 1) (· ∈ S)).symm (1, k.val)

omit [CompactSpace (AdeleQuotient F)] in
theorem awayFinite_at_S (k : awayIntegralSubgroup F (r + 1) S) (v : S) :
    localProjection F (r + 1) v (awayFinite S k) = 1 :=
  localProjection_splitAtPlaces_symm_of_pos F (r + 1) (· ∈ S) _ v.property

omit [CompactSpace (AdeleQuotient F)] in
theorem awayFinite_integral (k : awayIntegralSubgroup F (r + 1) S)
    (v : FinitePlace F) (hv : v ∉ S) :
    localProjection F (r + 1) v (awayFinite S k) ∈ localIntegral F (r + 1) v := by
  rw [awayFinite, localProjection_splitAtPlaces_symm_of_neg F (r + 1) (· ∈ S) _ hv]
  exact k.property ⟨v, hv⟩

omit [CompactSpace (AdeleQuotient F)] in
/-- The group decomposition's away point is exactly the same finite adelic inclusion. -/
theorem adelicSplit_away (k : awayIntegralSubgroup F (r + 1) S) :
    adelicSplit F (r + 1) S (1, (1, k.val)) =
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) (awayFinite S k)) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [adelicEquiv_adelicSplit, MulEquiv.apply_symm_apply, map_one]
  rfl

/-- Right translation by the away factor leaves the actual global Whittaker function fixed. -/
theorem whittaker_mul_away
    (ψ : AddChar (Adeles F) ℂ) (a : ∀ v : S, P.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) (k : awayIntegralSubgroup F (r + 1) S) :
    cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))
        (g * adelicSplit F (r + 1) S (1, (1, k.val))) =
      cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g := by
  have hfixed := fullVector_fixed_away P hP S hPS a t (awayFinite S k)
    (awayFinite_at_S S k) (awayFinite_integral S k)
  have hW := UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F ψ T (awayFinite S k)
    (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g
  exact (congrArg (fun q : Points F (r + 1) => cuspWhittaker F T ψ
    (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) (g * q))
      (adelicSplit_away S k)).trans
        (hW.symm.trans (congrArg (fun x => cuspWhittaker F T ψ x g) hfixed))

/-- Keep the infinite and S components of a point and set every other component to one. -/
def retainedPoint (g : Points F (r + 1)) : Points F (r + 1) :=
  adelicSplit F (r + 1) S (((adelicSplit F (r + 1) S).symm g).1,
    (((adelicSplit F (r + 1) S).symm g).2.1, 1))

omit [CompactSpace (AdeleQuotient F)] in
private theorem retainedPoint_decomposition
    (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
    ∃ (n : unipotentAdelic F (r + 1)) (k : awayIntegralSubgroup F (r + 1) S),
      g = n.val * (retainedPoint S g * adelicSplit F (r + 1) S (1, (1, k.val))) := by
  obtain ⟨n, hn, k, hk, hsplit⟩ :=
    exists_unipotent_mul_mul_of_mem_unipotentIntegralOutside F (r + 1) S hg
  exact ⟨⟨n, hn⟩, ⟨k, hk⟩, hsplit.trans (mul_assoc _ _ _)⟩

/-- Opposite-character Whittaker products are invariant under adelic left unipotents. -/
theorem whittaker_pair_unipotent
    (T' : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (x : T.Space) (x' : T'.Space) (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ x (n.val * g) * cuspWhittaker F T' ψ⁻¹ x' (n.val * g) =
      cuspWhittaker F T ψ x g * cuspWhittaker F T' ψ⁻¹ x' g := by
  rw [Unfolding.cuspWhittaker_mul_left F T ψ hψ,
    Unfolding.cuspWhittaker_mul_left F T' ψ⁻¹ (Unfolding.isStandardAdditiveCharacter_inv F ψ hψ),
    UnramifiedWhittaker.genericCharacter_inv]
  have hchi : genericCharacter F r ψ (fun _ => 1) n ≠ 0 := by
    intro hz
    have h := Unfolding.norm_genericCharacter F r ψ hψ.2.2.2 (fun _ => 1) n
    rw [hz, norm_zero] at h
    exact zero_ne_one h
  calc
    _ = (genericCharacter F r ψ (fun _ => 1) n *
        (genericCharacter F r ψ (fun _ => 1) n)⁻¹) *
        (cuspWhittaker F T ψ x g * cuspWhittaker F T' ψ⁻¹ x' g) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hchi, one_mul]

/-- On the whole partial domain, outside-S coordinates disappear from the paired product
of the actual prescribed tensor vectors. -/
theorem whittaker_pair_eq_retained
    (T' : CuspidalOperatorRealization F r)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS' : P'.exceptional ⊆ S)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
    cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g *
      cuspWhittaker F T' ψ⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')) g =
    cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) (retainedPoint S g) *
      cuspWhittaker F T' ψ⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t'))
        (retainedPoint S g) := by
  let x : T.Space := P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)
  let x' : T'.Space := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')
  change cuspWhittaker F T ψ x g * cuspWhittaker F T' ψ⁻¹ x' g =
    cuspWhittaker F T ψ x (retainedPoint S g) * cuspWhittaker F T' ψ⁻¹ x' (retainedPoint S g)
  obtain ⟨nu, ku, hsplit'⟩ := retainedPoint_decomposition (F := F) (r := r) S g hg
  have hpair := whittaker_pair_unipotent (T := T) T' ψ hψ x x' nu
    (retainedPoint S g * adelicSplit F (r + 1) S (1, (1, ku.val)))
  have hright := congrArg₂ (fun z w : ℂ => z * w)
    (whittaker_mul_away P hP S hPS ψ a t (retainedPoint S g) ku)
    (whittaker_mul_away P' hP' S hPS' ψ⁻¹ a' t' (retainedPoint S g) ku)
  exact (congrArg (fun q : Points F (r + 1) =>
    cuspWhittaker F T ψ x q * cuspWhittaker F T' ψ⁻¹ x' q)
    hsplit').trans (hpair.trans hright)


/-- Paired actual tensor Whittaker products depend only on the retained partial coordinates. -/
def PartialDomainPairReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S),
  ∀
    (T' : CuspidalOperatorRealization F r)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS' : P'.exceptional ⊆ S)
    (ψ : AddChar (Adeles F) ℂ) (_hψ : IsStandardAdditiveCharacter F ψ)
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) (_hg : g ∈ unipotentIntegralOutside F (r + 1) S),
    cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g *
      cuspWhittaker F T' ψ⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')) g =
    cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) (retainedPoint S g) *
      cuspWhittaker F T' ψ⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t'))
        (retainedPoint S g)

/-- Remove all outside-S finite coordinates from the paired Whittaker product. -/
theorem partialDomainPairReduction : PartialDomainPairReductionStatement.{u, uQ} := by
  intro F _ _ _ r T P hP S hPS T' P' hP' hPS' ψ hψ a a' t t' g hg
  exact whittaker_pair_eq_retained P hP S hPS T' P' hP' hPS' ψ hψ a a' t t' g hg

end Langlands.Global.RankinSelbergGlobal.FiniteWhittakerPartialDomain
