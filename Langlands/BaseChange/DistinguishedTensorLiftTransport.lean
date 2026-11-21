import Langlands.Automorphic.PresentedLocalCategory
import Langlands.BaseChange.CyclicGlobalizationPlaceComparison
import Langlands.BaseChange.SigmaLiftFieldEquivTransport
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.Global.CompletionPadic

/-! # The distinguished tensor sigma-lift at its unique completion -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.BaseChange

open Automorphic GeneralLinear Global Global.AdelicFunctoriality Global.CompletionPadic
open scoped FiniteExtension TensorProduct

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

local instance tensorLiftRationalGroup (M : Type u) [Field M] [NumberField M] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions M n) := Submodule.addCommGroup _
local instance tensorLiftContinuousGroup (M : Type u) [Field M] [NumberField M] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions M n) := Submodule.addCommGroup _
local instance tensorLiftSmoothGroup (M : Type u) [Field M] [NumberField M] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions M n) := Submodule.addCommGroup _
local instance tensorLiftFormsGroup (M : Type u) [Field M] [NumberField M] (n : ℕ) :
    AddCommGroup (AutomorphicForms M n) := Submodule.addCommGroup _
local instance tensorLiftLocalGroup {M : Type u} [Field M] [NumberField M]
    {n : ℕ} {v : FinitePlace M} (A : LocalRealization M n v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

/-- The unique completion isomorphism has the canonical tensor projection
as its underlying ring homomorphism. -/
theorem tensorUniqueCompletion_toRingHom_eq {v : FinitePlace K}
    (w : FinitePlacesAbove L v) (hw : ∀ z : FinitePlacesAbove L v, z = w) :
    (tensorUniqueCompletion v w hw).toRingHom =
      (Pi.evalRingHom (fun q : FinitePlacesAbove L v => q.1.adicCompletion L) w).comp
        (finiteTensorMap v).toRingHom := rfl

/-- The actual local components at the distinguished completions satisfy the
distributional lift for the specified upper automorphism. -/
def IsLiftAtDistinguishedCompletion {r : ℕ} {v : FinitePlace K} (w : FinitePlacesAbove L v)
    (τ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (l : ℕ)
    (A : LocalRealization K (r + 1) v) (B : LocalRealization L (r + 1) w.1)
    (hA : A.IsAdmissible) (hB : B.IsAdmissible) : Prop :=
  letI : ValuativeRel (v.adicCompletion K) := (topologicalData v).valuativeRel
  haveI : IsNonarchimedeanLocalField (v.adicCompletion K) := (topologicalData v).localField
  letI : ValuativeRel (w.1.adicCompletion L) := (topologicalData w.1).valuativeRel
  haveI : IsNonarchimedeanLocalField (w.1.adicCompletion L) := (topologicalData w.1).localField
  haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
  haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
  haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace (v.adicCompletion K) (r + 1)
  haveI := LocalFieldTopology.generalLinear_t2Space (w.1.adicCompletion L) (r + 1)
  haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (w.1.adicCompletion L) (r + 1)
  haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace (w.1.adicCompletion L) (r + 1)
  ∃ (J : SigmaIntertwiner τ (r + 1) B.representation) (c : ℂ),
    IsSigmaLift τ l A.representation hA B.representation hB J c

/-- The upper completion action pulled back through the unique tensor projection
is a distributional sigma-lift for the tensor automorphism. -/
def IsLiftAtDistinguishedTensor {r : ℕ} {v : FinitePlace K}
    (w : FinitePlacesAbove L v) (hw : ∀ z : FinitePlacesAbove L v, z = w)
    (σ : L ≃ₐ[K] L) (l : ℕ) (A : LocalRealization K (r + 1) v) (B : LocalRealization L (r + 1) w.1) : Prop :=
  let F := v.adicCompletion K
  let D := F ⊗[K] L
  letI : ValuativeRel F := (topologicalData v).valuativeRel
  haveI : IsNonarchimedeanLocalField F := (topologicalData v).localField
  letI : TopologicalSpace D := moduleTopology F D
  haveI : IsModuleTopology F D := ⟨rfl⟩
  haveI : IsTopologicalRing D := IsModuleTopology.isTopologicalRing F D
  haveI := LocalFieldTopology.generalLinear_t2Space F (r + 1)
  haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (r + 1)
  haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (r + 1)
  haveI := generalLinear_t2Space_of_finite F D (r + 1)
  haveI := generalLinear_locallyCompactSpace_of_finite F D (r + 1)
  haveI := generalLinear_totallyDisconnectedSpace_of_finite F D (r + 1)
  let τ : D ≃ₐ[F] D := Algebra.TensorProduct.congr AlgEquiv.refl σ
  let Bt := B.representation.comp (Matrix.GeneralLinearGroup.map (tensorUniqueCompletion v w hw).toRingHom)
  ∃ (hA : IsAdmissible A.representation) (hBt : IsAdmissible Bt) (I : SigmaIntertwiner τ (r + 1) Bt) (c : ℂ),
    IsSigmaLift τ l A.representation hA Bt hBt I c

/-- At the unique place above `v`, the tensor lift condition implies the
completion lift condition with the actual completed automorphism. -/
def DistinguishedTensorLiftTransportStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] (r : ℕ) (v : FinitePlace K) (w : FinitePlacesAbove L v)
    (hw : ∀ z : FinitePlacesAbove L v, z = w) (σ : L ≃ₐ[K] L) (l : ℕ)
    (A : LocalRealization K (r + 1) v) (B : LocalRealization L (r + 1) w.1)
    (hA : A.IsAdmissible) (hB : B.IsAdmissible),
    IsLiftAtDistinguishedTensor w hw σ l A B →
    IsLiftAtDistinguishedCompletion w (uniquePlaceCompletionAutEquiv w hw σ) l A B hA hB

set_option maxHeartbeats 6500000 in
theorem distinguishedTensorLiftTransport : DistinguishedTensorLiftTransportStatement.{u} := by
  intro K L _ _ _ _ _ _ r v w hw σ l A B hA hB hLift
  let F := v.adicCompletion K
  let E := w.1.adicCompletion L
  let D := F ⊗[K] L
  let e := tensorUniqueCompletion v w hw
  let : Field D := (e.toRingEquiv.toMulEquiv.isField (Field.toIsField E)).toField
  let : ValuativeRel F := (topologicalData v).valuativeRel
  let : IsNonarchimedeanLocalField F := (topologicalData v).localField
  let : ValuativeRel E := (topologicalData w.1).valuativeRel
  let : IsNonarchimedeanLocalField E := (topologicalData w.1).localField
  let : TopologicalSpace D := moduleTopology F D
  let : IsModuleTopology F D := ⟨rfl⟩
  let : IsTopologicalRing D := IsModuleTopology.isTopologicalRing F D
  let (n : ℕ) : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let (n : ℕ) : TotallyDisconnectedSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let (n : ℕ) : T2Space (GeneralLinear n E) := LocalFieldTopology.generalLinear_t2Space E n
  let (n : ℕ) : LocallyCompactSpace (GeneralLinear n E) := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  let (n : ℕ) : TotallyDisconnectedSpace (GeneralLinear n E) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
  let (n : ℕ) : T2Space (GeneralLinear n D) := generalLinear_t2Space_of_finite F D n
  let (n : ℕ) : LocallyCompactSpace (GeneralLinear n D) := generalLinear_locallyCompactSpace_of_finite F D n
  let (n : ℕ) : TotallyDisconnectedSpace (GeneralLinear n D) :=
    generalLinear_totallyDisconnectedSpace_of_finite F D n
  let τ : D ≃ₐ[F] D := Algebra.TensorProduct.congr AlgEquiv.refl σ
  let τ' := uniquePlaceCompletionAutEquiv w hw σ
  obtain ⟨hA', hBt, I, c, h⟩ := hLift
  obtain ⟨he, he'⟩ := tensorUniqueCompletion_bicontinuous v w hw
  let a := RingEquiv.refl F
  let b := e.symm.toRingEquiv
  have ha : Continuous a := continuous_id
  have ha' : Continuous a.symm := continuous_id
  have hmap : Continuous (algebraMap F E) := FiniteExtension.continuous_completionMap v w.1
  have hmap' : Continuous (algebraMap F D) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F D)
  have hσ (x : E) : b (τ' x) = τ (b x) := by
    apply e.injective
    change e (e.symm (τ' x)) = e (τ (e.symm x))
    have hc : e (τ (e.symm x)) = τ' (e (e.symm x)) := tensorUniqueCompletion_congr v w hw σ (e.symm x)
    rw [hc, e.apply_symm_apply, e.apply_symm_apply]
  obtain ⟨hAc, hBc, J, -, hj⟩ := sigmaLiftFieldEquivTransport F E F D (r + 1) l a b ha ha'
    he' he hmap hmap' (fun x => e.symm.commutes x) τ' τ hσ
    A.representation _ hA' hBt I c h
  let aG := fieldEquiv (r + 1) a ha ha'
  let eG := fieldEquiv (r + 1) e.toRingEquiv he he'
  have hAc' : A.representation.comp aG.toMonoidHom = A.representation := by
    apply MonoidHom.ext
    intro g
    change A.representation ((Matrix.GeneralLinearGroup.map (RingHom.id F)) g) = A.representation g
    rw [Matrix.GeneralLinearGroup.map_id]
    rfl
  have hBc' : (B.representation.comp eG.toMonoidHom).comp eG.symm.toMonoidHom = B.representation :=
    MonoidHom.ext fun g => congrArg B.representation (eG.apply_symm_apply g)
  let dA := equivOfRepresentationEq hAc'
  let dB := equivOfRepresentationEq hBc'
  exact ⟨J.transport dB, c, hj.transport hA dA hB dB⟩

end Langlands.BaseChange
