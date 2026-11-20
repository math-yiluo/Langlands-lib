import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction

/-! # Identifying a full-degree completion with the scalar-extension tensor product -/

noncomputable section

universe u

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.Global.AdelicFunctoriality

variable {F B : Type u} [Field F] [Field B] [NumberField F] [NumberField B] [Algebra F B]

private theorem eval_bijective_of_finrank_eq {K S : Type u} [Field K] [CommRing S]
    [Algebra K S] [FiniteDimensional K S] {I : Type u} {D : I → Type u}
    [∀ i, Field (D i)] [∀ i, Algebra K (D i)]
    (p : S →ₐ[K] (∀ i, D i)) (hp : Function.Surjective p) (i : I)
    [FiniteDimensional K (D i)]
    (h : Module.finrank K S = Module.finrank K (D i)) :
    Function.Bijective ((Pi.evalAlgHom K D i).comp p) := by
  classical
  have hs : Function.Surjective ((Pi.evalAlgHom K D i).comp p) := by
    intro x
    obtain ⟨t, ht⟩ := hp (Pi.single i x)
    exact ⟨t, by change p t i = x; rw [ht, Pi.single_eq_same]⟩
  exact OrzechProperty.bijective_of_surjective_of_finrank_le
    ((Pi.evalAlgHom K D i).comp p).toLinearMap hs h.le

/-- At a finite place of full local degree, the canonical tensor evaluation to the
selected completion is an algebra isomorphism. -/
def finiteCompletionTensorEquiv (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 B))
    [hw : w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion F) (w.adicCompletion B) = Module.finrank F B) :
    v.adicCompletion F ⊗[F] B ≃ₐ[v.adicCompletion F] w.adicCompletion B := by
  let : FiniteDimensional (v.adicCompletion F) (w.adicCompletion B) :=
    FiniteExtension.local_finite v w
  let p : FinitePlacesAbove B v := ⟨w, hw⟩
  apply AlgEquiv.ofBijective ((Pi.evalAlgHom _ _ p).comp (finiteTensorMap v))
  apply eval_bijective_of_finrank_eq (finiteTensorMap v) (finiteTensorMap_surjective v) p
  rw [Module.finrank_baseChange]
  exact h.symm

/-- The finite completion identification uses the selected tensor multiplication map. -/
theorem finiteCompletionTensorEquiv_tmul (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 B))
    [w.asIdeal.LiesOver v.asIdeal] (h : Module.finrank (v.adicCompletion F) (w.adicCompletion B) =
      Module.finrank F B) (x : v.adicCompletion F) (y : B) :
    finiteCompletionTensorEquiv v w h (x ⊗ₜ[F] y) =
      algebraMap (v.adicCompletion F) (w.adicCompletion B) x * algebraMap B (w.adicCompletion B) y := rfl

/-- At an infinite place of full local degree, the canonical tensor evaluation to the
selected completion is an algebra isomorphism. -/
def infiniteCompletionTensorEquiv (v : InfinitePlace F) (w : InfinitePlace B) [hw : w.LiesOver v]
    (h : Module.finrank v.Completion w.Completion = Module.finrank F B) :
    v.Completion ⊗[F] B ≃ₐ[v.Completion] w.Completion := by
  let p : InfinitePlacesAbove B v := ⟨w, hw⟩
  apply AlgEquiv.ofBijective ((Pi.evalAlgHom _ _ p).comp (infiniteTensorMap v))
  apply eval_bijective_of_finrank_eq (infiniteTensorMap v) (infiniteTensorMap_surjective v) p
  rw [Module.finrank_baseChange]
  exact h.symm

/-- The infinite completion identification uses the selected tensor multiplication map. -/
theorem infiniteCompletionTensorEquiv_tmul (v : InfinitePlace F) (w : InfinitePlace B) [w.LiesOver v]
    (h : Module.finrank v.Completion w.Completion = Module.finrank F B)
    (x : v.Completion) (y : B) :
    infiniteCompletionTensorEquiv v w h (x ⊗ₜ[F] y) =
      algebraMap v.Completion w.Completion x * algebraMap B w.Completion y := rfl

end Langlands.Global.AdelicFunctoriality
