import Langlands.Automorphic.CuspidalPlaceTensorDecomposition
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.PresentedLocalCategory
import Langlands.Representation.RestrictedTensor.Irreducibility
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.TensorProduct.MultiplicityCancellation
import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals

/-! # Tensor decomposition for a supplied cuspidal spectral presentation -/

noncomputable section
universe u uQ
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped TensorProduct

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

private theorem nonempty_equiv_of_nonzero_into_tensor
    {G Q A M : Type*} [Group G]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup M] [Module ℂ M]
    (σ : Representation ℂ G Q) (ρ : Representation ℂ G A)
    [σ.IsIrreducible] [ρ.IsIrreducible]
    (j : σ.IntertwiningMap (ρ.tprod (Representation.trivial ℂ G M))) (hj : j ≠ 0) :
    Nonempty (σ.Equiv ρ) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, j x ≠ 0 := by
    by_contra! h
    exact hj (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨i, hi⟩ := TensorMultiplicity.exists_coefficient_ne_zero ρ hx
  let f : σ.IntertwiningMap ρ :=
    (TensorMultiplicity.coefficient ρ (Module.Free.chooseBasis ℂ M) i).comp j
  have hf : f ≠ 0 := fun h => hi (congrArg (fun f : σ.IntertwiningMap ρ => f x) h)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

private theorem nonempty_equiv_of_injective_into_isotypic
    {G Q A M W : Type*} [Group G]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G Q) (ρ : Representation ℂ G A) (τ : Representation ℂ G W)
    [σ.IsIrreducible] [ρ.IsIrreducible]
    (q : (ρ.tprod (Representation.trivial ℂ G M)).Equiv τ)
    (j : σ.IntertwiningMap τ) (hj : Function.Injective j) : Nonempty (σ.Equiv ρ) := by
  let : Nontrivial Q := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : Q)
  let f := q.symm.toIntertwiningMap.comp j
  apply nonempty_equiv_of_nonzero_into_tensor σ ρ f
  intro hz
  apply hx
  apply hj
  apply q.symm.injective
  simpa [f] using congrArg (fun f : σ.IntertwiningMap
    (ρ.tprod (Representation.trivial ℂ G M)) => f x) hz

variable {F : Type u} [Field F] [NumberField F]
  [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance presentationTensorRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance presentationTensorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance presentationTensorSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance presentationTensorFormsGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance presentationTensorStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance presentationTensorSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _
local instance presentationTensorFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace CuspidalSpectralPresentation

variable (P : CuspidalSpectralPresentation.{u, uQ} T)

/-- All-place irreducible admissible local factors make the supplied finite slice irreducible. -/
theorem finiteSlice_isIrreducible
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) :
    P.finiteSlice.subspace.IsIrreducible := by
  let ρ := fun v => (P.localFactor v).representation
  have hI : ∀ v, (ρ v).IsIrreducible := fun v =>
    (P.presentation.localComponent_isIrreducible_iff P.finiteSlice.nonzero v).mp (hP v).1
  have hA : ∀ v, IsAdmissible (ρ v) := fun v =>
    (P.presentation.localComponent_isAdmissible_iff P.finiteSlice.nonzero v).mp (hP v).2
  let := hI
  have hir := Langlands.RestrictedTensor.representation_isIrreducible
    (fun v => (localIntegral F (r + 1) v).toSubgroup) ρ P.tensorExceptional
    P.reference P.reference_fixed P.presentation.reference_nonzero
    (fun v f => (admissibleSchur_scalarEndomorphism (ρ v) (hA v) (hI v) f).exists)
  have hfin : (tensorRepresentation F (r + 1) ρ P.tensorExceptional P.reference
      P.reference_fixed).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff _ (restrictedProductEquiv F (r + 1))).mpr hir
  exact CountableDual.isIrreducible_of_equiv _ P.presentation.equiv hfin

/-- The supplied finite slice is included in the actual full carrier. -/
def fullFiniteSliceInclusion :
    P.finiteSlice.subspace.representation.IntertwiningMap T.realization.finiteRepresentation :=
  T.realization.finiteEquiv.symm.toIntertwiningMap.comp P.finiteSlice.inclusion

theorem fullFiniteSliceInclusion_injective : Function.Injective P.fullFiniteSliceInclusion :=
  T.realization.finiteEquiv.symm.injective.comp P.finiteSlice.inclusion_injective

/-- The supplied irreducible finite slice is equivalent to the chosen actual finite factor. -/
theorem nonempty_finiteSliceEquiv
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) :
    Nonempty (P.finiteSlice.subspace.representation.Equiv
      T.finiteInfiniteDecomposition.finite.toRepresentation) := by
  let A := T.finiteInfiniteDecomposition
  let M := T.realization.FiniteMultiplicity A.finite
  let q : (A.finite.toRepresentation.tprod
      (Representation.trivial ℂ (FiniteAdelicGL F (r + 1)) M)).Equiv
      T.realization.finiteRepresentation :=
    Representation.Equiv.mk A.equiv (fun d => by
      apply LinearMap.ext
      intro t
      exact T.realization.finiteMultiplicityEvaluation_finite A.finite d t)
  let := P.finiteSlice_isIrreducible hP
  let := A.irreducible
  exact nonempty_equiv_of_injective_into_isotypic _ _ _ q P.fullFiniteSliceInclusion
    P.fullFiniteSliceInclusion_injective

/-- Admissibility of the actual factor transfers to the supplied finite spectral slice. -/
theorem finiteSlice_isAdmissible
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) :
    IsAdmissible P.finiteSlice.subspace.representation := by
  obtain ⟨e⟩ := P.nonempty_finiteSliceEquiv hP
  exact isAdmissible_of_equiv e.symm T.finiteInfiniteDecomposition.admissible

/-- Choose the equivalence from the supplied finite slice to the actual finite factor. -/
def finiteSliceEquiv
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) :
    P.finiteSlice.subspace.representation.Equiv
      T.finiteInfiniteDecomposition.finite.toRepresentation :=
  Classical.choice (P.nonempty_finiteSliceEquiv hP)

/-- The finite restricted tensor representation of this exact spectral presentation. -/
abbrev finiteTensorRepresentation :=
  tensorRepresentation F (r + 1) (fun v => (P.localFactor v).representation)
    P.tensorExceptional P.reference P.reference_fixed

/-- The supplied finite tensor is the chosen actual finite factor, equivariantly. -/
def finiteTensorEquiv
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) :
    P.finiteTensorRepresentation.Equiv T.finiteInfiniteDecomposition.finite.toRepresentation :=
  P.presentation.equiv.trans (P.finiteSliceEquiv hP)

/-- The given finite tensor and all actual infinite source factors recover the carrier. -/
def allPlaceTensorEquiv
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) :
    Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
        P.tensorExceptional P.reference ⊗[ℂ]
      (⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) ≃ₗ[ℂ] T.Space :=
  (TensorProduct.congr (P.finiteTensorEquiv hP).toLinearEquiv (LinearEquiv.refl ℂ _)).trans
    T.allPlaceTensorEquiv

/-- Prescribed finite vectors transform by the given finite spectral tensor representation. -/
theorem allPlaceTensorEquiv_finite
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (d : FiniteAdelicGL F (r + 1))
    (a : Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
      P.tensorExceptional P.reference)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
    P.allPlaceTensorEquiv hP ((P.finiteTensorRepresentation d a) ⊗ₜ[ℂ] t) =
      T.realization.finiteRepresentation d (P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] t)) := by
  change T.allPlaceTensorEquiv ((P.finiteTensorEquiv hP (P.finiteTensorRepresentation d a)) ⊗ₜ[ℂ] t) =
    T.realization.finiteRepresentation d
      (T.allPlaceTensorEquiv ((P.finiteTensorEquiv hP a) ⊗ₜ[ℂ] t))
  have hmap := Representation.IntertwiningMap.isIntertwining _ _
    (P.finiteTensorEquiv hP).toIntertwiningMap d a
  apply (congrArg (fun v : T.finiteInfiniteDecomposition.finite.toSubmodule =>
    T.allPlaceTensorEquiv (v ⊗ₜ[ℂ] t)) hmap).trans
  exact T.placeDensityModels.fullTensorEquiv_finite T.finiteInfiniteDecomposition.finite
    T.irreducible T.finiteInfiniteDecomposition.nonzero
    T.finiteInfiniteDecomposition.irreducible T.finiteInfiniteDecomposition.admissible d _ t

/-- The presentation-based equivalence also retains every local compact action. -/
theorem allPlaceTensorEquiv_compact
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (i : InfinitePlaceFamily.Index F) (k : InfinitePlaceFamily.Compact (r + 1) i)
    (a : Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
      P.tensorExceptional P.reference)
    (b c : ∀ j, T.placeDensityModels.subspace j)
    (hother : ∀ j, j ≠ i → c j = b j)
    (hlocal : c i = T.placeDensityModels.sourceCompact i k (b i)) :
    P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      T.realization.placeCompactFamily i k
        (P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) :=
  T.placeDensityModels.fullTensorEquiv_compact T.finiteInfiniteDecomposition.finite
    T.irreducible T.finiteInfiniteDecomposition.nonzero
    T.finiteInfiniteDecomposition.irreducible T.finiteInfiniteDecomposition.admissible
    i k (P.finiteTensorEquiv hP a) b c hother hlocal

/-- The presentation-based equivalence retains every local Lie action. -/
theorem allPlaceTensorEquiv_lie
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (i : InfinitePlaceFamily.Index F) (X : InfinitePlaceFamily.Lie (r + 1) i)
    (a : Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
      P.tensorExceptional P.reference)
    (b c : ∀ j, T.placeDensityModels.subspace j)
    (hother : ∀ j, j ≠ i → c j = b j)
    (hlocal : c i = T.placeDensityModels.sourceLie i X (b i)) :
    P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      T.realization.placeLieFamily i X
        (P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) :=
  T.placeDensityModels.fullTensorEquiv_lie T.finiteInfiniteDecomposition.finite
    T.irreducible T.finiteInfiniteDecomposition.nonzero
    T.finiteInfiniteDecomposition.irreducible T.finiteInfiniteDecomposition.admissible
    i X (P.finiteTensorEquiv hP a) b c hother hlocal

/-- Nonzero prescribed finite tensors and nonzero infinite pure factors stay nonzero. -/
theorem allPlaceTensorEquiv_pure_ne_zero
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (a : Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
      P.tensorExceptional P.reference) (b : ∀ j, T.placeDensityModels.subspace j)
    (ha : a ≠ 0) (hb : ∀ i, b i ≠ 0) :
    P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) ≠ 0 := by
  have hqa : P.finiteTensorEquiv hP a ≠ 0 := fun h =>
    ha ((P.finiteTensorEquiv hP).injective
      (h.trans (map_zero (P.finiteTensorEquiv hP).toLinearEquiv).symm))
  exact T.placeDensityModels.fullTensorEquiv_pure_ne_zero T.finiteInfiniteDecomposition.finite
    T.irreducible T.finiteInfiniteDecomposition.nonzero
    T.finiteInfiniteDecomposition.irreducible T.finiteInfiniteDecomposition.admissible
    (P.finiteTensorEquiv hP a) b hqa hb

/-- Insert arbitrary prescribed factors at a finite set containing the exceptional set. -/
def finitePure (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
    (a : ∀ v : S, P.localFactor v) :
    Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
      P.tensorExceptional P.reference :=
  Langlands.RestrictedTensor.pure P.tensorExceptional P.reference
    ⟨S, P.unramified.exceptional_subset.trans hPS⟩ a

/-- Every prescribed nonzero finite tuple gives a nonzero finite tensor. -/
theorem finitePure_ne_zero (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
    (a : ∀ v : S, P.localFactor v) (ha : ∀ v, a v ≠ 0) : P.finitePure S hPS a ≠ 0 := by
  intro hz
  apply Langlands.RestrictedTensor.stage_tprod_ne_zero (K := ℂ)
    (V := fun v => P.localFactor v) S a ha
  apply Langlands.RestrictedTensor.of_injective (K := ℂ) (V := fun v => P.localFactor v)
    P.tensorExceptional P.reference
    P.presentation.reference_nonzero ⟨S, P.unramified.exceptional_subset.trans hPS⟩
  exact hz.trans (map_zero _).symm

/-- The prescribed finite tuple is fixed by every integral subgroup outside its support. -/
theorem finitePure_fixed (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
    (a : ∀ v : S, P.localFactor v) (v : FinitePlace F) (hv : v ∉ S)
    (k : FiniteLocalGL F (r + 1) v) (hk : k ∈ localIntegral F (r + 1) v) :
    P.finiteTensorRepresentation (localInclusion F (r + 1) v k) (P.finitePure S hPS a) =
      P.finitePure S hPS a := by
  have hlocal : ∀ w ∉ S, localProjection F (r + 1) w (localInclusion F (r + 1) v k) ∈
      localIntegral F (r + 1) w := by
    intro w _
    by_cases hw : w = v
    · subst w
      rwa [localProjection_localInclusion]
    · rw [localProjection_localInclusion_of_ne F (r + 1) v w hw]
      exact (localIntegral F (r + 1) w).one_mem
  change P.finiteTensorRepresentation (localInclusion F (r + 1) v k)
    (Langlands.RestrictedTensor.pure P.tensorExceptional P.reference
      ⟨S, P.unramified.exceptional_subset.trans hPS⟩ a) = _
  rw [tensorRepresentation_pure_of_mem F (r + 1) (fun w => (P.localFactor w).representation)
    P.tensorExceptional P.reference P.reference_fixed _ _ hlocal]
  congr 1
  funext w
  have hw : w.val ≠ v := fun h => hv (h ▸ w.property)
  rw [localProjection_localInclusion_of_ne F (r + 1) v w hw, map_one, Module.End.one_apply]

/-- Every vector built from these prescribed finite factors is spherical outside their support. -/
theorem allPlaceTensorEquiv_finitePure_sphericalOutside
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
    (a : ∀ v : S, P.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
    Langlands.Global.RankinSelbergGlobal.IsSphericalOutside F T S
      (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) := by
  intro v hv k hk
  exact (P.allPlaceTensorEquiv_finite hP (localInclusion F (r + 1) v k)
    (P.finitePure S hPS a) t).symm.trans
      (congrArg (fun a => P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] t))
        (P.finitePure_fixed S hPS a v hv k hk))

/-- The genuine finite, local compact and local Lie covariance of the presentation tensor. -/
def IsPlaceTensorEquivalence
    (e : Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
        P.tensorExceptional P.reference ⊗[ℂ]
      (⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) ≃ₗ[ℂ] T.Space) : Prop :=
  (∀ d a t, e ((P.finiteTensorRepresentation d a) ⊗ₜ[ℂ] t) =
    T.realization.finiteRepresentation d (e (a ⊗ₜ[ℂ] t))) ∧
  (∀ i k a (b c : ∀ j, T.placeDensityModels.subspace j),
    (∀ j, j ≠ i → c j = b j) → c i = T.placeDensityModels.sourceCompact i k (b i) →
    e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      T.realization.placeCompactFamily i k (e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b))) ∧
  ∀ i X a (b c : ∀ j, T.placeDensityModels.subspace j),
    (∀ j, j ≠ i → c j = b j) → c i = T.placeDensityModels.sourceLie i X (b i) →
    e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      T.realization.placeLieFamily i X (e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b))

/-- Every supplied all-place irreducible admissible presentation has the actual full tensor form. -/
def PresentationPlaceTensorStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (P : CuspidalSpectralPresentation.{u, uQ} T),
    (∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible) →
    P.finiteSlice.subspace.IsIrreducible ∧ IsAdmissible P.finiteSlice.subspace.representation ∧
    ∃ e : Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v)
        P.tensorExceptional P.reference ⊗[ℂ]
      (⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) ≃ₗ[ℂ] T.Space,
      P.IsPlaceTensorEquivalence e

/-- The all-place carrier decomposition on the exact supplied finite presentation. -/
theorem presentationPlaceTensor : PresentationPlaceTensorStatement.{u, uQ} := by
  intro K _ _ _ r T P hP
  exact ⟨P.finiteSlice_isIrreducible hP, P.finiteSlice_isAdmissible hP,
    P.allPlaceTensorEquiv hP, P.allPlaceTensorEquiv_finite hP,
    P.allPlaceTensorEquiv_compact hP, P.allPlaceTensorEquiv_lie hP⟩

end CuspidalSpectralPresentation
end Langlands.Automorphic
