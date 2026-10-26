import Langlands.Representation.Smooth.Factorization.CyclicSelectionProof
import Langlands.Representation.RestrictedTensor.CyclicEvaluationEquivariant
import Langlands.Representation.Smooth.Schur.Proof

/-! # Flath factorization for the actual restricted product -/

noncomputable section
open scoped Classical

namespace Langlands

open RestrictedTensor RestrictedTensor.CyclicEvaluation

universe uI uG uV

/-- An irreducible admissible restricted-product representation has the actual
restricted tensor factorization, with local carriers in its own universe. -/
theorem flathRestrictedProductExistence :
    FlathRestrictedProductExistenceStatement.{uI, uG, uV} := by
  intro ι G _ _ _ _ _ _ _ _ μ _ _ H V _ _ π hH hcomm hadm hirr
  let := hirr
  obtain ⟨E, v, hv0, hv, hgood, hsph⟩ :=
    flathCyclicVectorSelection ι G μ H V π hH hcomm hadm hirr
  let W (i : ι) : ModuleCat.{uV} ℂ :=
    ModuleCat.of ℂ (Factor (localAction H π) v i)
  let ρ (i : ι) : Representation ℂ (G i) (W i) :=
    (Cyclic.orbitSpan (localAction H π i) v).toRepresentation
  let e (i : ι) : W i := Cyclic.generator (localAction H π i) v
  have he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i := by
    intro i hi g hg
    apply Subtype.ext
    exact (hsph i hi).1 ⟨g, hg⟩
  let r : ReferenceVectors (fun i => W i) E :=
    { vector := fun i _ => e i
      nonzero := fun i _ h => hv0 (congrArg Subtype.val h) }
  have hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i,
      ρ i g (r.vector i hi) = r.vector i hi := he
  refine ⟨W, ρ, hgood, E, r, hr, fun i hi => (hsph i hi).2, ?_⟩
  have htail : ∀ t ∈ tailReferenceSubgroup H E, π t v = v :=
    fun t ht => hv t ht.1 ht.2
  have hscalar : ∀ i, ∀ f : (ρ i).IntertwiningMap (ρ i),
      ∃ c : ℂ, f = c • Representation.IntertwiningMap.id (ρ i) :=
    fun i f => (admissibleSchur_scalarEndomorphism (ρ i)
      (hgood i).1 (hgood i).2 f).exists
  let ev : (tensorAction H π v E he).Equiv π :=
    evalEquiv H π v E he htail hv0 (fun i => (hgood i).2) hscalar
  have href : ∀ᶠ i in Filter.cofinite, e i = r.family i :=
    E.eventually_cofinite_notMem.mono fun i hi =>
      (ReferenceVectors.family_of_not_mem r hi).symm
  let refEquiv : (tensorAction H π v E he).Equiv
      (productRepresentation H ρ E r hr) :=
    Representation.Equiv.mk (change E E e r.family href) (by
      intro g
      exact map_intertwines H ρ ρ E E e r.family he
        (fun i hi a ha => by
          simpa only [ReferenceVectors.family_of_not_mem r hi] using hr i hi a ha)
        (fun _ => LinearMap.id) href (fun _ _ => rfl) g)
  exact ⟨ev.symm.trans refEquiv⟩

end Langlands
