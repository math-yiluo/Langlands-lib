import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Representation.Whittaker.RestrictedTensorProportionality

/-! # Whittaker uniqueness for the finite adelic factor -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace Langlands.Global.FiniteAdelicGL

open Langlands.RestrictedTensor Langlands.Whittaker MeasureTheory
  Langlands.Global.RankinSelbergGlobal.FiniteWhittakerTensor
open scoped Classical

universe u uV

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "N" v => GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)

/-- A linear functional has the prescribed Whittaker character under the
actual insertion of each local upper unipotent group. -/
def HasWhittakerComponents
    (ψ : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) V) (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ (v : FinitePlace F) (a : N v) (w : V),
    ℓ (ρ (localInclusion F (r + 1) v a.val) w) = (factorCharacter v (ψ v) a : ℂ) * ℓ w

private theorem localFunctionals_proportional (v : FinitePlace F)
    (ψ : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible)
    (f g : V →ₗ[ℂ] ℂ) (hf : f ∈ functionals (N v) (factorCharacter v ψ) ρ)
    (hg : g ∈ functionals (N v) (factorCharacter v ψ) ρ) (hne : f ≠ 0) :
    ∃ c : ℂ, g = c • f := by
  have hAc : @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) V _ _ _ _
      ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)) ρ := by
    rw [← localGL_topology_eq F v (r + 1)]
    exact hA
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  let := (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel
  let := (CompletionPadic.padicField v).canonicalTopologicalData.localField
  obtain ⟨c, hc⟩ := (localFieldMultiplicityOne _ r V ψ ρ hAc hI ⟨f, hf⟩ ⟨g, hg⟩ hne).exists
  exact ⟨c, congrArg Subtype.val hc⟩

private theorem proportional_of_tensorComponents
    (W : FinitePlace F → Type uV) [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
    (τ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (W v))
    (hτ : ∀ v, IsAdmissible (τ v) ∧ (τ v).IsIrreducible)
    (E : Finset (FinitePlace F)) (e : ∀ v, W v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, τ v g (e v) = e v)
    (ψ : ∀ v, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (f g : Space ℂ W E e →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (hfψ : HasWhittakerComponents ψ (tensorRepresentation F (r + 1) τ E e he) f)
    (hgψ : HasWhittakerComponents ψ (tensorRepresentation F (r + 1) τ E e he) g) :
    ∃ c : ℂ, g = c • f := by
  let Λ (v : FinitePlace F) := functionals (N v) (factorCharacter v (ψ v)) (τ v)
  have hslot (ℓ : Space ℂ W E e →ₗ[ℂ] ℂ)
      (hℓ : HasWhittakerComponents ψ (tensorRepresentation F (r + 1) τ E e he) ℓ)
      (S : Index E) (b : ∀ i : S.1, W i) (i : S.1) :
      (stageFunctional E e ℓ S).toLinearMap b i ∈ Λ i := by
    intro a w
    have hact := tensorRepresentation_localInclusion_pure F (r + 1) τ E e he
      i.val a.val S i.property (Function.update b i w)
    simp only [Function.update_self, Function.update_idem] at hact
    simp only [MultilinearMap.toLinearMap_apply, stageFunctional_apply]
    rw [← hact]
    exact hℓ i a (pure E e S (Function.update b i w))
  exact proportional_of_stageFunctionals E e Λ
    (fun v => localFunctionals_proportional v (ψ v) (τ v) (hτ v).1 (hτ v).2)
    f g hf (hslot f hfψ) (hslot g hgψ)

/-- Local Whittaker uniqueness compares two functionals on any irreducible
admissible finite adelic factor. Only the prescribed single-place
covariance identities enter the comparison. -/
theorem finiteAdelicWhittakerMultiplicityOne
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) V)
    (hA : IsAdmissible ρ) (hI : ρ.IsIrreducible)
    (ψ : ∀ v, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (f g : V →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (hfψ : HasWhittakerComponents ψ ρ f) (hgψ : HasWhittakerComponents ψ ρ g) :
    ∃ c : ℂ, g = c • f := by
  have htop := fun v => localGL_flathTopology (F := F) v r
  let : ∀ v, T2Space (FiniteLocalGL F (r + 1) v) := fun v => (htop v).1
  let : ∀ v, LocallyCompactSpace (FiniteLocalGL F (r + 1) v) := fun v => (htop v).2.1
  let : ∀ v, TotallyDisconnectedSpace (FiniteLocalGL F (r + 1) v) := fun v => (htop v).2.2.1
  let : ∀ v, MeasurableSpace (FiniteLocalGL F (r + 1) v) := fun v => borel _
  let : ∀ v, BorelSpace (FiniteLocalGL F (r + 1) v) := fun v => ⟨rfl⟩
  choose μ hμH hμR hμC using fun v => localGL_exists_sphericalHeckeCommutative (F := F) v r
  let : ∀ v, (μ v).IsHaarMeasure := hμH
  let : ∀ v, (μ v).Regular := hμR
  let H := fun v => (localIntegral F (r + 1) v).toSubgroup
  let π : Representation ℂ (RestrictedGroup (fun v => FiniteLocalGL F (r + 1) v) H) V :=
    ρ.comp (restrictedProductEquiv F (r + 1)).symm.toMonoidHom
  have hπA : IsAdmissible π :=
    isAdmissible_comp_continuousMulEquiv ρ (restrictedProductEquiv F (r + 1)).symm hA
  have hπI : π.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff ρ (restrictedProductEquiv F (r + 1)).symm).mpr hI
  obtain ⟨W, τ, hτ, E, refs, hfix, _, ⟨eq⟩⟩ :=
    flathRestrictedProductExistence (FinitePlace F)
      (fun v => FiniteLocalGL F (r + 1) v) μ H V π
      (fun v => ⟨(localIntegral F (r + 1) v).isOpen, (htop v).2.2.2⟩)
      (Filter.Eventually.of_forall hμC) hπA hπI
  have href : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, τ v g (refs.family v) = refs.family v := by
    intro v hv d hd
    rw [ReferenceVectors.family_of_not_mem refs hv]
    exact hfix v hv d hd
  let P := tensorRepresentation F (r + 1) τ E refs.family href
  let e : P.Equiv ρ := Representation.Equiv.mk eq.symm.toLinearEquiv (fun d => by
    apply LinearMap.ext
    intro x
    have h := Representation.IntertwiningMap.isIntertwining _ _ eq.symm.toIntertwiningMap
      (restrictedProductEquiv F (r + 1) d) x
    refine h.trans ?_
    change ρ ((restrictedProductEquiv F (r + 1)).symm (restrictedProductEquiv F (r + 1) d)) _ = _
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl)
  let f' := f.comp e.toLinearEquiv.toLinearMap
  let g' := g.comp e.toLinearEquiv.toLinearMap
  have hpull (ℓ : V →ₗ[ℂ] ℂ) (hℓ : HasWhittakerComponents ψ ρ ℓ) :
      HasWhittakerComponents ψ P (ℓ.comp e.toLinearEquiv.toLinearMap) := by
    intro v a w
    change ℓ (e (P (localInclusion F (r + 1) v a.val) w)) =
      (factorCharacter v (ψ v) a : ℂ) * ℓ (e w)
    have he := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
      (localInclusion F (r + 1) v a.val) w
    exact (congrArg ℓ he).trans (hℓ v a (e w))
  have hne : f' ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro w
    obtain ⟨z, rfl⟩ := e.toLinearEquiv.surjective w
    exact LinearMap.congr_fun h z
  obtain ⟨c, hc⟩ := proportional_of_tensorComponents (fun v => W v) τ hτ E refs.family href ψ f' g' hne
    (hpull f hfψ) (hpull g hgψ)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  obtain ⟨z, rfl⟩ := e.toLinearEquiv.surjective w
  exact LinearMap.congr_fun hc z

end Langlands.Global.FiniteAdelicGL
