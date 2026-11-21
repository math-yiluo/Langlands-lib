import Langlands.BaseChange.CyclicGlobalizationPlaceComparison
import Langlands.Global.Factors.RelativeWeilAssemblyHecke

/-! # The actual distinguished completions in cyclic globalization -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality IsDedekindDomain
open Global.FunctionalEquationComparison
open scoped NumberField FiniteExtension TensorProduct

/-- The field tensor furnished by cyclic globalization determines a unique place.
The induced field isomorphism to its actual completion preserves the scalar
embedding and carries the specified local generator to the completed generator. -/
def DistinguishedCompletionGlobalizationStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] (p : FinitePlace K) (s : L ≃ₐ[K] L)
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] (σ : E ≃ₐ[F] E)
    (a : p.adicCompletion K ≃+* F) (b : p.adicCompletion K ⊗[K] L ≃+* E),
    Continuous a → Continuous a.symm →
    (∀ x : p.adicCompletion K, b (x ⊗ₜ[K] (1 : L)) = algebraMap F E (a x)) →
    (∀ y : p.adicCompletion K ⊗[K] L,
      b (Algebra.TensorProduct.congr (AlgEquiv.refl : p.adicCompletion K ≃ₐ[K] _) s y) = σ (b y)) →
    (letI := moduleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
     Continuous b ∧ Continuous b.symm) →
    ∃ (w : FinitePlacesAbove L p) (hw : ∀ z : FinitePlacesAbove L p, z = w),
      RelativeWeilEngine.placesAbove L p = {w.1} ∧
      ∃ e : E ≃+* w.1.adicCompletion L,
        Continuous e ∧ Continuous e.symm ∧
        (∀ x : F, e (algebraMap F E x) = algebraMap (p.adicCompletion K) (w.1.adicCompletion L) (a.symm x)) ∧
        (∀ x : E, e (σ x) = uniquePlaceCompletionAutEquiv w hw s (e x))

set_option maxHeartbeats 900000 in
/-- Compose the tensor identification with the actual projection and use the
compatibility of that projection with the global automorphism. -/
theorem distinguishedCompletionGlobalization : DistinguishedCompletionGlobalizationStatement.{u, v} := by
  classical
  intro K L _ _ _ _ _ _ p s F E _ _ _ _ _ σ a b _ _ hab hσ hb
  obtain ⟨w, hw⟩ := (cyclicGlobalizationPlaceComparison K L p s 1).1 E b
  let e := tensorUniqueCompletion p w hw
  let ε := b.symm.trans e.toRingEquiv
  have hsingle : RelativeWeilEngine.placesAbove L p = {w.1} := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hz
      rw [hw y]
      exact Finset.mem_singleton_self _
    · intro hz
      rw [Finset.mem_singleton.mp hz]
      exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩
  let := moduleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
  obtain ⟨he, he'⟩ := tensorUniqueCompletion_bicontinuous p w hw
  refine ⟨w, hw, hsingle, ε, he.comp hb.2, hb.1.comp he', ?_, ?_⟩
  · intro x
    have hx : b.symm (algebraMap F E x) = a.symm x ⊗ₜ[K] (1 : L) := by
      apply b.injective
      rw [b.apply_symm_apply, hab, a.apply_symm_apply]
    change e (b.symm (algebraMap F E x)) = _
    rw [hx, tensorUniqueCompletion_tmul, map_one, mul_one]
  · intro x
    have hx : b.symm (σ x) =
        Algebra.TensorProduct.congr (AlgEquiv.refl : p.adicCompletion K ≃ₐ[K] _) s (b.symm x) := by
      apply b.injective
      rw [b.apply_symm_apply, hσ, b.apply_symm_apply]
    change e (b.symm (σ x)) = uniquePlaceCompletionAutEquiv w hw s (e (b.symm x))
    rw [hx]
    exact tensorUniqueCompletion_congr p w hw s (b.symm x)

end Langlands.BaseChange
