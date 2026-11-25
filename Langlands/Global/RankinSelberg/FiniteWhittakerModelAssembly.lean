import Langlands.Global.RankinSelberg.FiniteWhittakerTensor
import Langlands.Automorphic.PadicLocalCategory

/-! # Prescribed embedded local coefficient vectors in the finite Whittaker tensor -/

noncomputable section
open scoped TensorProduct Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ uG uV uW

namespace Langlands.Global.RankinSelbergGlobal.FiniteWhittakerModel

section Abstract

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  (e : ρ.Equiv σ) {N : Subgroup G} {θ : N →* ℂˣ}

/-- Pull a genuine equivariant functional back through a genuine representation equivalence. -/
def pullbackFunctional (ℓ : Whittaker.functionals N θ σ) : Whittaker.functionals N θ ρ :=
  ⟨ℓ.val.comp e.toLinearEquiv.toLinearMap, fun n v => by
    change ℓ.val (e (ρ n.val v)) = (θ n : ℂ) * ℓ.val (e v)
    exact (congrArg ℓ.val (Representation.IntertwiningMap.isIntertwining _ _
      e.toIntertwiningMap n.val v)).trans (ℓ.property n (e v))⟩

theorem pullbackFunctional_ne_zero (ℓ : Whittaker.functionals N θ σ) (hℓ : ℓ.val ≠ 0) :
    (pullbackFunctional e ℓ).val ≠ 0 := by
  intro hz
  apply hℓ
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  exact LinearMap.congr_fun hz v

/-- Every prescribed coefficient-model function is exactly realized by a source vector. -/
theorem exists_coefficient_vector (ℓ : Whittaker.functionals N θ σ)
    (f : (Whittaker.coefficientModel σ ℓ).toSubmodule) :
    ∃ v : V, ∀ g : G, (pullbackFunctional e ℓ).val (ρ g v) = f.val.val g := by
  obtain ⟨w, hw⟩ := Whittaker.modelMap_surjective σ ℓ f
  refine ⟨e.symm w, fun g => ?_⟩
  change ℓ.val (e (ρ g (e.symm w))) = f.val.val g
  have hmap := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g (e.symm w)
  exact (congrArg ℓ.val hmap).trans
    ((congrArg (fun x => ℓ.val (σ g x)) (e.apply_symm_apply w)).trans
      (congrArg (fun f : (Whittaker.coefficientModel σ ℓ).toSubmodule => f.val.val g) hw))

/-- A vector realizing a nonzero coefficient-model function cannot vanish. -/
theorem coefficient_vector_ne_zero (ℓ : Whittaker.functionals N θ ρ)
    (f : (Whittaker.coefficientModel ρ ℓ).toSubmodule) (a : V)
    (ha : ∀ g : G, ℓ.val (ρ g a) = f.val.val g) (hf : f ≠ 0) : a ≠ 0 := by
  intro hz
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change f.val.val g = 0
  rw [← ha, hz, map_zero, map_zero]

/-- A nonzero linear functional admits a vector on which it takes the value one. -/
theorem normalizedVector {A : Type*} [AddCommGroup A] [Module ℂ A]
    (ℓ : A →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) : ∃ a, ℓ a = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, ℓ a ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  exact ⟨(ℓ a)⁻¹ • a, by simp [ha]⟩

end Abstract

open Langlands.Automorphic Langlands.Global.FiniteAdelicGL FiniteWhittakerTensor

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance finiteModelSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance finiteModelSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance finiteModelRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteModelContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteModelSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteModelFormsGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteModelStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteModelSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _
local instance finiteModelLocalGroup {v : FinitePlace F} (L : LocalRealization F (r + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

variable (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
  (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)

/-- Functionals on the original embedded local component, with the canonical character. -/
abbrev ComponentFunctionals (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) :=
  Whittaker.functionals
    (Langlands.GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier)
    (factorCharacter (r := r) v ψv) (P.localComponent v).representation

/-- Transport an embedded local Whittaker functional to the exact supplied tensor factor. -/
def factorFunctional (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ℓ : ComponentFunctionals P v ψv) : FactorFunctionals P v ψv :=
  pullbackFunctional (P.presentation.localComponentEquiv P.finiteSlice.nonzero v) ℓ

theorem factorFunctional_ne_zero (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ℓ : ComponentFunctionals P v ψv) (hℓ : ℓ.val ≠ 0) :
    (factorFunctional P v ψv ℓ).val ≠ 0 :=
  pullbackFunctional_ne_zero _ ℓ hℓ

/-- A prescribed embedded coefficient-model function has an exact source factor vector. -/
theorem exists_factorVector (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ℓ : ComponentFunctionals P v ψv)
    (f : (Whittaker.coefficientModel (P.localComponent v).representation ℓ).toSubmodule) :
    ∃ a : P.localFactor v, ∀ h : FiniteLocalGL F (r + 1) v,
      (factorFunctional P v ψv ℓ).val ((P.localFactor v).representation h a) = f.val.val h :=
  exists_coefficient_vector _ ℓ f

/-- Choose a supplied-factor vector realizing the prescribed embedded coefficient function. -/
def factorVectorData (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ℓ : ComponentFunctionals P v ψv)
    (f : (Whittaker.coefficientModel (P.localComponent v).representation ℓ).toSubmodule) :
    {a : P.localFactor v // ∀ h : FiniteLocalGL F (r + 1) v,
      (factorFunctional P v ψv ℓ).val ((P.localFactor v).representation h a) = f.val.val h} :=
  ⟨Classical.choose (exists_factorVector P v ψv ℓ f),
    Classical.choose_spec (exists_factorVector P v ψv ℓ f)⟩

/-- Nonzero prescribed embedded coefficient functions give nonzero factor vectors. -/
theorem factorVectorData_ne_zero (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ℓ : ComponentFunctionals P v ψv)
    (f : (Whittaker.coefficientModel (P.localComponent v).representation ℓ).toSubmodule)
    (hf : f ≠ 0) : (factorVectorData P v ψv ℓ f).val ≠ 0 := by
  intro hz
  have hzero : f = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val g = 0
    rw [← (factorVectorData P v ψv ℓ f).property g, hz, map_zero, map_zero]
  exact hf hzero

/-- Actual finite-place factorization for any prescribed embedded coefficient-model vectors. -/
theorem exists_prescribed_modelVectors
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, ComponentFunctionals P v.1 (ψv v))
    (hℓ : ∀ v, (ℓ v).val ≠ 0)
    (f : ∀ v : S, (Whittaker.coefficientModel (P.localComponent v).representation (ℓ v)).toSubmodule) :
    ∃ a a₀ : ∀ v : S, P.localFactor v,
      (∀ v : S, (factorFunctional P v.1 (ψv v) (ℓ v)).val (a₀ v) = 1) ∧
      (∀ (v : S) (h : FiniteLocalGL F (r + 1) v),
        (factorFunctional P v.1 (ψv v) (ℓ v)).val ((P.localFactor v).representation h (a v)) =
          (f v).val.val h) ∧
      (∀ t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u),
        IsSphericalOutside F T S
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))) ∧
      (∀ b : ∀ i, T.placeDensityModels.subspace i,
        (∀ v : S, f v ≠ 0) → (∀ i, b i ≠ 0) →
        P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) ≠ 0) ∧
      ∀ (g : Points F (r + 1)), (∀ v : S, finiteComponent F (r + 1) v g = 1) →
      ∀ (d : FiniteAdelicGL F (r + 1)),
      (∀ v ∉ S, localProjection F (r + 1) v d ∈ localIntegral F (r + 1) v) →
      ∀ t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u),
      cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))
          (g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
            (AdelicGL.ofFinite F (r + 1) d)) =
        (∏ v : S, (f v).val.val (localProjection F (r + 1) v d)) *
          cuspWhittaker F T ψ.complex
            (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) g := by
  classical
  let a : ∀ v : S, P.localFactor v :=
    fun v => (factorVectorData P v.1 (ψv v) (ℓ v) (f v)).val
  have ha (v : S) (h : FiniteLocalGL F (r + 1) v.1) :
      (factorFunctional P v.1 (ψv v) (ℓ v)).val ((P.localFactor v).representation h (a v)) =
        (f v).val.val h :=
    (factorVectorData P v.1 (ψv v) (ℓ v) (f v)).property h
  let ℓfactor : ∀ v : S, FactorFunctionals P v.1 (ψv v) :=
    fun v => factorFunctional P v.1 (ψv v) (ℓ v)
  choose a₀ ha₀ using fun v : S => normalizedVector (ℓfactor v).val
    (factorFunctional_ne_zero P v.1 (ψv v) (ℓ v) (hℓ v))
  refine ⟨a, a₀, ha₀, ha, ?_, ?_, fun g hg d hd t => ?_⟩
  · exact fun t => P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS a t
  · intro b hf hb
    exact P.allPlaceTensorEquiv_pure_ne_zero hP (P.finitePure S hPS a) b
      (P.finitePure_ne_zero S hPS a
        (fun v => factorVectorData_ne_zero P v.1 (ψv v) (ℓ v) (f v) (hf v))) hb
  · have h := translated_coefficient_eq_product P hP S hPS ψ hψF ψv hψv ℓfactor a₀ ha₀ g hg d hd t a
    have hlocal : (∏ v : S, (ℓfactor v).val ((P.localFactor v).representation
          (localProjection F (r + 1) v d) (a v))) =
        ∏ v : S, (f v).val.val (localProjection F (r + 1) v d) :=
      Finset.prod_congr rfl (fun v _ => ha v _)
    exact h.trans (congrArg (fun c : ℂ => c * cuspWhittaker F T ψ.complex
      (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) g) hlocal)

/-- Exact assembly of prescribed embedded finite coefficient functions on an actual global vector. -/
def PrescribedModelVectorAssemblyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S),
  ∀
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (_hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (_hψv : ∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, ComponentFunctionals P v.1 (ψv v))
    (_hℓ : ∀ v, (ℓ v).val ≠ 0)
    (f : ∀ v : S, (Whittaker.coefficientModel (P.localComponent v).representation (ℓ v)).toSubmodule),
    ∃ a a₀ : ∀ v : S, P.localFactor v,
      (∀ v : S, (factorFunctional P v.1 (ψv v) (ℓ v)).val (a₀ v) = 1) ∧
      (∀ (v : S) (h : FiniteLocalGL F (r + 1) v),
        (factorFunctional P v.1 (ψv v) (ℓ v)).val ((P.localFactor v).representation h (a v)) =
          (f v).val.val h) ∧
      (∀ t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u),
        IsSphericalOutside F T S
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))) ∧
      (∀ b : ∀ i, T.placeDensityModels.subspace i,
        (∀ v : S, f v ≠ 0) → (∀ i, b i ≠ 0) →
        P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) ≠ 0) ∧
      ∀ (g : Points F (r + 1)), (∀ v : S, finiteComponent F (r + 1) v g = 1) →
      ∀ (d : FiniteAdelicGL F (r + 1)),
      (∀ v ∉ S, localProjection F (r + 1) v d ∈ localIntegral F (r + 1) v) →
      ∀ t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u),
      cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))
          (g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
            (AdelicGL.ofFinite F (r + 1) d)) =
        (∏ v : S, (f v).val.val (localProjection F (r + 1) v d)) *
          cuspWhittaker F T ψ.complex
            (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) g

/-- The prescribed model-vector assembly is implemented by genuine local equivalences. -/
theorem finiteWhittakerModelAssembly : PrescribedModelVectorAssemblyStatement.{u, uQ} := by
  intro F _ _ _ r T P hP S hPS ψ hψF ψv hψv ℓ hℓ f
  exact exists_prescribed_modelVectors P hP S hPS ψ hψF ψv hψv ℓ hℓ f

end Langlands.Global.RankinSelbergGlobal.FiniteWhittakerModel
