import Langlands.Automorphic.CuspidalPresentationTensorDecomposition
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof

/-! # Finite-place separation of the actual cuspidal Whittaker functional -/

noncomputable section
open scoped TensorProduct Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ uI uV

namespace Langlands.Global.RankinSelbergGlobal.FiniteWhittakerTensor

section Multilinear

variable {I : Type uI} [Fintype I] {A : I → Type uV}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]

/-- A multilinear form whose local slices lie on specified normalized lines is a product. -/
theorem multilinear_eq_product
    (L : MultilinearMap ℂ A ℂ) (ℓ : ∀ i, A i →ₗ[ℂ] ℂ) (a₀ : ∀ i, A i)
    (ha₀ : ∀ i, ℓ i (a₀ i) = 1)
    (hline : ∀ i a, ∃ c : ℂ, L.toLinearMap a i = c • ℓ i) (a : ∀ i, A i) :
    L a = (∏ i, ℓ i (a i)) * L a₀ := by
  classical
  have hslot (i : I) (b : ∀ i, A i) (x : A i) :
      L (Function.update b i x) = ℓ i x * L (Function.update b i (a₀ i)) := by
    obtain ⟨c, hc⟩ := hline i b
    have hx := LinearMap.congr_fun hc x
    have hy := LinearMap.congr_fun hc (a₀ i)
    simp only [MultilinearMap.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul] at hx hy
    rw [ha₀, mul_one] at hy
    rw [hx, hy, mul_comm]
  let b : Finset I → ∀ i, A i := fun s i => if i ∈ s then a i else a₀ i
  have hfinite : ∀ s : Finset I, L (b s) = (∏ i ∈ s, ℓ i (a i)) * L a₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [b]
    | insert i s hi ih =>
      have hinsert : b (insert i s) = Function.update (b s) i (a i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [b]
        · simp [b, hji]
      have hreset : Function.update (b s) i (a₀ i) = b s := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [b, hi]
        · simp [hji]
      rw [hinsert, hslot, hreset, ih, Finset.prod_insert hi, mul_assoc]
  simpa [b] using hfinite Finset.univ

end Multilinear

open Langlands.Automorphic Langlands.Global.FiniteAdelicGL

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance finiteWhittakerTensorSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance finiteWhittakerTensorSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance finiteWhittakerTensorRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteWhittakerTensorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteWhittakerTensorSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteWhittakerTensorFormsGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteWhittakerTensorStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteWhittakerTensorSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _

variable (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
  (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)

/-- The actual full carrier vector, multilinear in the prescribed finite local factors. -/
def finitePureMultilinear
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
    MultilinearMap ℂ (fun v : S => P.localFactor v) T.Space :=
  ((P.allPlaceTensorEquiv hP).toLinearMap.comp
    (((TensorProduct.mk ℂ _ _).flip t).comp
      (Langlands.RestrictedTensor.of ℂ (fun v => P.localFactor v)
        P.tensorExceptional P.reference ⟨S, P.unramified.exceptional_subset.trans hPS⟩))).compMultilinearMap
          (PiTensorProduct.tprod ℂ)

@[simp] theorem finitePureMultilinear_apply
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) (a : ∀ v : S, P.localFactor v) :
    finitePureMultilinear P hP S hPS t a =
      P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t) := rfl

/-- Local insertion changes precisely one coordinate of the actual finite pure tensor. -/
theorem finitePureMultilinear_update
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) (a : ∀ v : S, P.localFactor v)
    (v : S) (h : FiniteLocalGL F (r + 1) v) :
    finitePureMultilinear P hP S hPS t (Function.update a v ((P.localFactor v).representation h (a v))) =
      T.realization.finiteRepresentation (localInclusion F (r + 1) v h)
        (finitePureMultilinear P hP S hPS t a) := by
  have hact := tensorRepresentation_localInclusion_pure F (r + 1)
    (fun v => (P.localFactor v).representation) P.tensorExceptional P.reference P.reference_fixed
    v h ⟨S, P.unramified.exceptional_subset.trans hPS⟩ v.property a
  exact (congrArg (fun z => P.allPlaceTensorEquiv hP (z ⊗ₜ[ℂ] t)) hact.symm).trans
    (P.allPlaceTensorEquiv_finite hP (localInclusion F (r + 1) v h) (P.finitePure S hPS a) t)

/-- The actual global Whittaker coefficient, multilinear in the finite tensor factors. -/
def whittakerMultilinear (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (g : Points F (r + 1))
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
    MultilinearMap ℂ (fun v : S => P.localFactor v) ℂ :=
  (UnramifiedWhittaker.whittakerFunctional F ψ hψ T g).compMultilinearMap
    (finitePureMultilinear P hP S hPS t)

@[simp] theorem whittakerMultilinear_apply
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (g : Points F (r + 1))
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) (a : ∀ v : S, P.localFactor v) :
    whittakerMultilinear P hP S hPS ψ hψ g t a =
      cuspWhittaker F T ψ (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g := rfl

/-- At a base point trivial at the selected finite place, each slot is a genuine local
Whittaker functional for the matching global character. -/
theorem whittakerMultilinear_slot_mem
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (v : S) (g : Points F (r + 1))
    (θ : Langlands.GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField (K := F) v.1).Carrier →* ℂˣ)
    (hglobal : UnramifiedWhittaker.whittakerFunctional F ψ hψ T g ∈
      Whittaker.functionals
        (Langlands.GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField (K := F) v.1).Carrier)
        θ (T.realization.localRepresentation v))
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (a : ∀ v : S, P.localFactor v) :
    (whittakerMultilinear P hP S hPS ψ hψ g t).toLinearMap a v ∈
      Whittaker.functionals
        (Langlands.GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField (K := F) v.1).Carrier)
        θ (P.localFactor v).representation := by
  intro u x
  have hact := finitePureMultilinear_update P hP S hPS t (Function.update a v x) v u.val
  have hmem := hglobal u (finitePureMultilinear P hP S hPS t (Function.update a v x))
  have h := (congrArg (UnramifiedWhittaker.whittakerFunctional F ψ hψ T g) hact).trans hmem
  simpa [whittakerMultilinear, MultilinearMap.toLinearMap_apply] using h

/-- The local standard character of a supplied canonical finite additive component. -/
def factorCharacter (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) :
    Langlands.GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier →* ℂˣ := by
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  exact Whittaker.standardCharacter ψv r

/-- Actual Whittaker functionals on the exact local factor supplied by the presentation. -/
abbrev FactorFunctionals (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) :=
  Whittaker.functionals
    (Langlands.GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier)
    (factorCharacter (r := r) v ψv) (P.localFactor v).representation

include hP in
/-- The published local multiplicity-one theorem applies to the exact supplied factors. -/
theorem factorFunctionals_eq_smul (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ℓ₀ ℓ₁ : FactorFunctionals P v ψv) (hℓ₀ : ℓ₀.val ≠ 0) :
    ∃ c : ℂ, ℓ₁ = c • ℓ₀ := by
  let ρ := (P.localFactor v).representation
  have hI : ρ.IsIrreducible :=
    (P.presentation.localComponent_isIrreducible_iff P.finiteSlice.nonzero v).mp (hP v).1
  have hA : IsAdmissible ρ :=
    (P.presentation.localComponent_isAdmissible_iff P.finiteSlice.nonzero v).mp (hP v).2
  have hAc : @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) (P.localFactor v) _ _ _ _
      ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)) ρ := by
    rw [← localGL_topology_eq F v (r + 1)]
    exact hA
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  let := (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel
  let := (CompletionPadic.padicField v).canonicalTopologicalData.localField
  exact (Whittaker.localFieldMultiplicityOne _ r _ ψv ρ hAc hI ℓ₀ ℓ₁ hℓ₀).exists

/-- Finite factors separate from a joint residual Whittaker coefficient at every base
point whose components at S are the identity. -/
theorem coefficient_eq_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v, (ℓ v).val (a₀ v) = 1)
    (g : Points F (r + 1)) (hg : ∀ v : S, finiteComponent F (r + 1) v g = 1)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (a : ∀ v : S, P.localFactor v) :
    cuspWhittaker F T ψ.complex
        (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g =
      (∏ v : S, (ℓ v).val (a v)) *
        cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) g := by
  classical
  let hψ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψF
  apply multilinear_eq_product (whittakerMultilinear P hP S hPS ψ.complex hψ g t)
    (fun v => (ℓ v).val) a₀ ha₀
  intro v b
  have hglobal := UnramifiedWhittaker.whittakerFunctional_mem F ψ.complex hψ T v.1 g (hg v)
    (UnramifiedWhittaker.genericCharacter_localPoint F ψ v.1 (ψv v) (hψv v))
  let ℓb : FactorFunctionals P v.1 (ψv v) :=
    ⟨(whittakerMultilinear P hP S hPS ψ.complex hψ g t).toLinearMap b v,
      whittakerMultilinear_slot_mem P hP S hPS ψ.complex hψ v g
        (factorCharacter (r := r) v.1 (ψv v)) hglobal t b⟩
  have hℓ : (ℓ v).val ≠ 0 := by
    intro hz
    have h := ha₀ v
    rw [hz, LinearMap.zero_apply] at h
    exact zero_ne_one h
  obtain ⟨c, hc⟩ := factorFunctionals_eq_smul P hP v.1 (ψv v) (ℓ v) ℓb hℓ
  refine ⟨c, ?_⟩
  have hcval := congrArg Subtype.val hc
  change ℓb.val = c • (ℓ v).val at hcval
  dsimp only [ℓb] at hcval
  apply LinearMap.ext
  intro x
  have hcx := LinearMap.congr_fun hcval x
  simp only [MultilinearMap.toLinearMap_apply, LinearMap.smul_apply] at hcx ⊢
  convert hcx using 2
  congr 2
  exact Subsingleton.elim _ _

/-- Finite local coefficient functions factor at a base point trivial on S, while the
infinite variables remain in one actual residual global Whittaker coefficient. -/
theorem translated_coefficient_eq_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v, (ℓ v).val (a₀ v) = 1)
    (g : Points F (r + 1)) (hg : ∀ v : S, finiteComponent F (r + 1) v g = 1)
    (d : FiniteAdelicGL F (r + 1))
    (hd : ∀ v ∉ S, localProjection F (r + 1) v d ∈ localIntegral F (r + 1) v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (a : ∀ v : S, P.localFactor v) :
    cuspWhittaker F T ψ.complex
        (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))
        (g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
          (AdelicGL.ofFinite F (r + 1) d)) =
      (∏ v : S, (ℓ v).val ((P.localFactor v).representation
        (localProjection F (r + 1) v d) (a v))) *
        cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) g := by
  let b : ∀ v : S, P.localFactor v :=
    fun v => (P.localFactor v).representation (localProjection F (r + 1) v d) (a v)
  have hact := tensorRepresentation_pure_of_mem F (r + 1)
    (fun v => (P.localFactor v).representation) P.tensorExceptional P.reference P.reference_fixed
    d ⟨S, P.unramified.exceptional_subset.trans hPS⟩ hd a
  have hvec := (congrArg (fun z => P.allPlaceTensorEquiv hP (z ⊗ₜ[ℂ] t)) hact.symm).trans
    (P.allPlaceTensorEquiv_finite hP d (P.finitePure S hPS a) t)
  have htrans := UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F ψ.complex T d
    (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g
  exact htrans.symm.trans
    ((congrArg (fun x => cuspWhittaker F T ψ.complex x g) hvec.symm).trans
      (coefficient_eq_product P hP S hPS ψ hψF ψv hψv ℓ a₀ ha₀ g hg t b))

private theorem exists_normalized_vector {A : Type*} [AddCommGroup A] [Module ℂ A]
    (ℓ : A →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) : ∃ a, ℓ a = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, ℓ a ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  exact ⟨(ℓ a)⁻¹ • a, by simp [ha]⟩

/-- Actual finite Whittaker separation on the exact supplied tensor presentation,
with one residual global coefficient retaining all infinite variables. -/
def FiniteWhittakerSeparationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (S : Finset (FinitePlace K)) (hPS : P.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)),
    (∀ x : K, ψ (algebraMap K (Adeles K) x) = 1) →
    ∀ (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1)),
    (∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v)) →
    ∀ (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v)),
    (∀ v, (ℓ v).val ≠ 0) →
    ∃ a₀ : ∀ v : S, P.localFactor v,
      (∀ v, (ℓ v).val (a₀ v) = 1) ∧
      ∀ (g : Points K (r + 1)), (∀ v : S, finiteComponent K (r + 1) v g = 1) →
      ∀ (d : FiniteAdelicGL K (r + 1)),
      (∀ v ∉ S, localProjection K (r + 1) v d ∈ localIntegral K (r + 1) v) →
      ∀ (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
        (a : ∀ v : S, P.localFactor v),
      cuspWhittaker K T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))
          (g * (GeneralLinearGroupPoints.adelicEquiv K (r + 1)).symm
            (AdelicGL.ofFinite K (r + 1) d)) =
        (∏ v : S, (ℓ v).val ((P.localFactor v).representation
          (localProjection K (r + 1) v d) (a v))) *
          cuspWhittaker K T ψ.complex
            (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) g

/-- Nonarchimedean local uniqueness separates every finite tensor factor in S. -/
theorem finiteWhittakerSeparation : FiniteWhittakerSeparationStatement.{u, uQ} := by
  intro K _ _ _ r T P hP S hPS ψ hψF ψv hψv ℓ hℓ
  choose a₀ ha₀ using fun v => exists_normalized_vector (ℓ v).val (hℓ v)
  exact ⟨a₀, ha₀, fun g hg d hd t a =>
    translated_coefficient_eq_product P hP S hPS ψ hψF ψv hψv ℓ a₀ ha₀ g hg d hd t a⟩

end Langlands.Global.RankinSelbergGlobal.FiniteWhittakerTensor
