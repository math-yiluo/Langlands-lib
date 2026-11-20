import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.OperatorScalarCentralCharacter
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Global.PositiveRealIdeles
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Common split-centre normalization for cuspidal realizations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped NNReal NumberField

universe u uQ

namespace Langlands.Global.CuspidalCommonSplitCentreTwist

open Automorphic
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)
open CuspidalPairPoles (IsPositiveArchimedeanScalar IsTrivialOnSplitCentre)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (V : OperatorRealization F n) : AddCommGroup V.Space :=
  Submodule.addCommGroup _
local instance {n : ℕ} {v : FinitePlace F} (V : LocalRealization F n v) : AddCommGroup V.Space :=
  Submodule.addCommGroup _

set_option maxHeartbeats 2000000 in
/-- Agreement of the finite components outside a finite set transports the central character. -/
theorem hasCentralCharacter_of_localClass_eq
    (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (heq : ∀ v ∉ S, localClass P h v = localClass P' h' v)
    (ω : HeckeCharacter F) (hω : T.HasCentralCharacter ω) : T'.HasCentralCharacter ω := by
  apply T'.realization.hasCentralCharacter_of_centralCharacterSubgroup_eq_top ω
  refine IdeleDensity.eq_top_of_isClosed _ S (T'.realization.isClosed_centralCharacterSubgroup ω)
    (T'.realization.diagonalUnits_mem_centralCharacterSubgroup ω) ?_
  intro v hv a
  obtain ⟨e⟩ := ((P.localComponent v).padicClass_eq_iff (P'.localComponent v)
    (h v).1 (h v).2 (h' v).1 (h' v).2).mp (heq v hv)
  have hn : (P.localComponent v).toSubmodule ≠ ⊥ := fun he =>
    P.localComponent_ne_bot v (Subrepresentation.toSubmodule_injective he)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let f : (P.localComponent v).Space := ⟨x, hx⟩
  have hf : f ≠ 0 := fun he => hx0 (congrArg Subtype.val he)
  let j := T.realization.localSubspaceInclusion v _ (P.localComponent_le_full v)
  let j' := T'.realization.localSubspaceInclusion v _ (P'.localComponent_le_full v)
  have hj := T.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v)
  have hj' := T'.realization.localSubspaceInclusion_injective v _ (P'.localComponent_le_full v)
  let g := Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a
  let c : ℂ := ω.finiteComponent v a
  have hacts : finiteIdeleInclusion F v a ∈ T.realization.centralCharacterSubgroup ω :=
    (T.realization.mem_centralCharacterSubgroup ω _).mpr fun b x =>
      T.realization.centralCharacter_evaluate ω hω b _ x
  have hlocal : (P.localComponent v).representation g f = c • f := by
    apply hj
    change j ((P.localComponent v).representation g f) = j (c • f)
    rw [Representation.IntertwiningMap.isIntertwining, map_smul]
    exact (T.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff ω v a).mp
      hacts (j f)
  have himage : j' (e f) ≠ 0 := by
    intro h0
    have hzero : j' (e (0 : (P.localComponent v).Space)) = 0 :=
      (congrArg j' (LinearEquiv.map_zero e.toLinearEquiv)).trans j'.toLinearMap.map_zero
    exact hf (e.injective (hj' (h0.trans hzero.symm)))
  have hlocal' : T'.realization.localRepresentation v g (j' (e f)) = c • j' (e f) := by
    calc
      _ = j' ((P'.localComponent v).representation g (e f)) :=
        (Representation.IntertwiningMap.isIntertwining _ _ j' g (e f)).symm
      _ = j' (e ((P.localComponent v).representation g f)) :=
        congrArg j' (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g f).symm
      _ = _ := by
        rw [hlocal]
        exact (j'.toLinearMap.comp e.toLinearEquiv.toLinearMap).map_smul c f
  exact (T'.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff ω v a).mpr
    (T'.realization.localScalar_eq_smul_of_ne_zero T'.irreducible v a c himage hlocal')

private def positiveRoot (k : ℕ) : ℝ≥0ˣ →ₜ* ℝ≥0ˣ where
  toMonoidHom := Units.map (NNReal.rpowMonoidHom ((k : ℝ)⁻¹))
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr <|
    (NNReal.continuous_rpow_const (inv_nonneg.mpr (Nat.cast_nonneg k))).comp Units.continuous_val

private theorem positiveRoot_pow {k : ℕ} (hk : k ≠ 0) (t : ℝ≥0ˣ) :
    positiveRoot k t ^ k = t := by
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow (t : ℝ≥0) hk

/-- The inverse of the central character evaluated on the positive root of the idelic norm. -/
def splitCentreNormalizingCharacter (ω : HeckeCharacter F) (r : ℕ) : HeckeCharacter F :=
  ((ω.onIdeles.comp (PositiveRealIdeles.full F)).comp
    ((positiveRoot (Module.finrank ℚ F * (r + 1))).comp (IdeleAbsoluteValue.ideleClass F)))⁻¹

omit [CompactSpace (AdeleQuotient F)] in
private theorem exists_eq_positiveRealIdele {a : Ideles F} (ha : IsPositiveArchimedeanScalar a) :
    ∃ t : ℝ≥0ˣ, a = PositiveRealIdeles.full F t := by
  obtain ⟨hfin, t, ht, hinf⟩ := ha
  let x : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (by exact pos_iff_ne_zero.mp ht)
  refine ⟨x, Units.ext (Prod.ext ?_ ?_)⟩
  · funext v
    apply (NumberField.InfinitePlace.Completion.extensionEmbedding v).injective
    rw [hinf v]
    exact (PositiveRealIdeles.extensionEmbedding_full F v x).symm
  · exact hfin

/-- The normalizing twist makes the split centre act trivially on a realization with
the prescribed central character. -/
theorem isTrivialOnSplitCentre_normalizingTwist (ω : HeckeCharacter F)
    (V : CuspidalOperatorRealization F r) (hV : V.HasCentralCharacter ω) :
    IsTrivialOnSplitCentre (V.heckeDeterminantTwist (splitCentreNormalizingCharacter ω r)) := by
  let k := Module.finrank ℚ F * (r + 1)
  have hk : k ≠ 0 := Nat.mul_ne_zero Module.finrank_pos.ne' (Nat.succ_ne_zero r)
  let χ := splitCentreNormalizingCharacter ω r
  have hcentral : (V.heckeDeterminantTwist χ).HasCentralCharacter (χ ^ (r + 1) * ω) := by
    change (V.realization.heckeDeterminantTwist χ).toFiniteRealization.HasCentralCharacter _
    rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
    exact V.realization.toFiniteRealization.heckeDeterminantTwist_hasCentralCharacter χ ω hV
  intro a ha f x
  obtain ⟨t, rfl⟩ := exists_eq_positiveRealIdele ha
  have hroot : positiveRoot k (t ^ Module.finrank ℚ F) ^ (r + 1) = t := by
    rw [← map_pow, ← pow_mul]
    change positiveRoot k (t ^ k) = t
    rw [map_pow, positiveRoot_pow hk]
  have ht : (χ ^ (r + 1) * ω) (ideleClassMap F (PositiveRealIdeles.full F t)) = 1 := by
    simp only [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply]
    change (ω.onIdeles (PositiveRealIdeles.full F
      (positiveRoot k (IdeleAbsoluteValue.ideleClass F (ideleClassMap F
        (PositiveRealIdeles.full F t))))))⁻¹ ^ (r + 1) *
      ω.onIdeles (PositiveRealIdeles.full F t) = 1
    rw [IdeleAbsoluteValue.ideleClass_class, PositiveRealIdeles.absoluteValue_full, inv_pow,
      ← map_pow, ← map_pow, hroot, inv_mul_cancel]
  have he := (V.heckeDeterminantTwist χ).realization.centralCharacter_evaluate _ hcentral f
    (PositiveRealIdeles.full F t) x
  change _ = (↑((χ ^ (r + 1) * ω) (ideleClassMap F (PositiveRealIdeles.full F t))) : ℂ) * _ at he
  simpa only [ht, Units.val_one, one_mul] using he

/-- A common central character admits one determinant twist trivializing the split
centre on every realization of the given rank with that character. -/
theorem exists_common_splitCentre_twist (ω : HeckeCharacter F) :
    ∃ χ : HeckeCharacter F, ∀ V : CuspidalOperatorRealization F r, V.HasCentralCharacter ω →
      IsTrivialOnSplitCentre (V.heckeDeterminantTwist χ) :=
  ⟨splitCentreNormalizingCharacter ω r, isTrivialOnSplitCentre_normalizingTwist ω⟩

/-- A common determinant twist preserves equality of the local classes of the presentations. -/
theorem twist_localClass_eq
    (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (χ : HeckeCharacter F) (v : FinitePlace F) (he : localClass P h v = localClass P' h' v) :
    localClass (P.heckeDeterminantTwist χ) (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h) v =
      localClass (P'.heckeDeterminantTwist χ) (P'.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h') v := by
  obtain ⟨e⟩ := ((P.localComponent v).padicClass_eq_iff (P'.localComponent v)
    (h v).1 (h v).2 (h' v).1 (h' v).2).mp he
  apply (LocalRealization.padicClass_eq_iff _ _ _ _ _ _).mpr
  exact ⟨(P.heckeDeterminantTwistLocalComponentEquiv χ v).trans
    (((P.localComponent v).heckeDeterminantTwistRepresentationEquiv χ).symm.trans
      ((Langlands.twistEquiv (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom e).trans
        (((P'.localComponent v).heckeDeterminantTwistRepresentationEquiv χ).trans
          (P'.heckeDeterminantTwistLocalComponentEquiv χ v).symm)))⟩

private theorem equivalence_of_commonConjugation
    {A V W V₁ W₁ : Type*} [Monoid A]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup W₁] [Module ℂ W₁]
    {ρ : Representation ℂ A V} {τ : Representation ℂ A W}
    {ρ₁ : Representation ℂ A V₁} {τ₁ : Representation ℂ A W₁}
    (α : A ≃* A) (L : V ≃ₗ[ℂ] V₁) (L' : W ≃ₗ[ℂ] W₁)
    (hL : ∀ a f, ρ₁ a (L f) = L (ρ (α a) f))
    (hL' : ∀ a f, τ₁ a (L' f) = L' (τ (α a) f))
    (e : ρ₁.Equiv τ₁) : Nonempty (ρ.Equiv τ) := by
  let φ := (L.trans e.toLinearEquiv).trans L'.symm
  have hφ (f : V) : L' (φ f) = e (L f) := L'.apply_symm_apply _
  refine ⟨Representation.Equiv.mk φ (fun a => LinearMap.ext fun f => ?_)⟩
  change φ (ρ a f) = τ a (φ f)
  obtain ⟨b, rfl⟩ := α.surjective a
  apply L'.injective
  rw [hφ, ← hL, ← hL', hφ]
  exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap b (L f)

/-- Full operator equivalence of a common determinant twist descends to the original pair. -/
theorem isoClass_eq_of_twist_eq (χ : HeckeCharacter F)
    (h : (T.heckeDeterminantTwist χ).isoClass = (T'.heckeDeterminantTwist χ).isoClass) :
    T.isoClass = T'.isoClass := by
  obtain ⟨e⟩ := ((T.heckeDeterminantTwist χ).isoClass_eq_iff _).mp h
  apply (T.isoClass_eq_iff T').mpr
  exact equivalence_of_commonConjugation (heckeDeterminantOperatorConjugation (r + 1) χ).toMulEquiv
    (T.realization.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T'.realization.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T.realization.heckeDeterminantTwistEquiv_operatorAction χ)
    (T'.realization.heckeDeterminantTwistEquiv_operatorAction χ) e

end Langlands.Global.CuspidalCommonSplitCentreTwist
