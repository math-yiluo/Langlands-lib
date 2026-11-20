import Langlands.Representation.RestrictedTensor.Maps
import Langlands.Representation.Tensor.SmoothDualInjectivityProof

/-!
# Pointwise evaluation of restricted tensors

Local families of linear evaluations induce evaluations with values in the
restricted coefficient tensor. Jointly faithful local evaluations distinguish
the global tensors when the coefficient references are nonzero.
-/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uK uI uX uA uV

namespace Langlands.RestrictedTensor

open Module

variable {K : Type uK} [Field K] {ι : Type uI}
variable {X : ι → Type uX} {A : ι → Type uA} {V : ι → Type uV}
variable [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable (ev : ∀ i, X i → A i →ₗ[K] V i)

private theorem finiteEvaluation_eq_zero [Fintype ι]
    (hsep : ∀ i (a : A i), (∀ x, ev i x a = 0) → a = 0)
    (z : ⨂[K] i, A i) (hz : ∀ x : ∀ i, X i, PiTensorProduct.map (fun i => ev i (x i)) z = 0) :
    z = 0 := by
  let Test (i : ι) := X i × Module.Dual K (V i)
  let D (i : ι) := Test i →₀ K
  let b (i : ι) : Basis (Test i) K (D i) := Finsupp.basisSingleOne
  let g (i : ι) : A i →ₗ[K] Module.Dual K (D i) :=
    ((b i).constr K fun p => p.2.comp (ev i p.1)).flip
  have hg (i : ι) (a : A i) (p : Test i) :
      g i a (b i p) = p.2 (ev i p.1 a) := by
    change (((b i).constr K fun p => p.2.comp (ev i p.1)) (b i p)) a = _
    rw [Basis.constr_basis, LinearMap.comp_apply]
  have hi (i : ι) : Function.Injective (g i) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    apply hsep i a
    intro x
    apply (Module.forall_dual_apply_eq_zero_iff K _).mp
    intro φ
    rw [← hg i a (x, φ), ha, LinearMap.zero_apply]
  let G : (⨂[K] i, A i) →ₗ[K] Module.Dual K (⨂[K] i, D i) :=
    PiTensorProduct.dualDistrib.comp (PiTensorProduct.map g)
  apply (injective_iff_map_eq_zero G).mp (FiniteTensor.dualDistrib_comp_map_injective g hi) z
  apply (Basis.piTensorProduct b).ext
  intro p
  rw [Basis.piTensorProduct_apply]
  have he :
      (Dual.eval K (⨂[K] i, D i) (PiTensorProduct.tprod K (fun i => b i (p i)))).comp G =
      (PiTensorProduct.dualDistrib (PiTensorProduct.tprod K (fun i => (p i).2))).comp
        (PiTensorProduct.map (fun i => ev i (p i).1)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, G,
      Dual.eval_apply, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply, hg]
  have hez := LinearMap.congr_fun he z
  change G z (PiTensorProduct.tprod K (fun i => b i (p i))) = _ at hez
  rw [hez, LinearMap.comp_apply, hz, map_zero, LinearMap.zero_apply]

variable (E : Finset ι) (a : ∀ i, A i) (b : ∀ i, V i)
  (href : ∀ i ∉ E, ∀ x, ev i x (a i) = b i)

/-- Evaluate at a family of local points using a bound shared by every evaluation. -/
def pointwiseEvaluation : Space K A E a →ₗ[K] ((∀ i, X i) → Space K V E b) :=
  LinearMap.pi fun x =>
    mapWithBound E E a b (fun i => ev i (x i)) E (Finset.Subset.refl _) fun i hi => href i hi (x i)

@[simp]
theorem pointwiseEvaluation_pure (S : Index E) (v : ∀ i : S.1, A i) (x : ∀ i, X i) :
    pointwiseEvaluation ev E a b href (pure E a S v) x =
      pure E b S (fun i => ev i (x i) (v i)) :=
  mapWithBound_pure_of_subset E E a b (fun i => ev i (x i)) E (Finset.Subset.refl _)
    (fun i hi => href i hi (x i)) S S.2 v

/-- Evaluation acts factorwise on any vector presented at a finite stage. -/
theorem pointwiseEvaluation_of (S : Index E) (v : Stage K A S.1) (x : ∀ i, X i) :
    pointwiseEvaluation ev E a b href (of K A E a S v) x =
      of K V E b S (PiTensorProduct.map (fun i : S.1 => ev i (x i)) v) := by
  have h :
      ((LinearMap.proj x).comp (pointwiseEvaluation ev E a b href)).comp (of K A E a S) =
      (of K V E b S).comp (PiTensorProduct.map (fun i : S.1 => ev i (x i))) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change pointwiseEvaluation ev E a b href (pure E a S w) x =
        of K V E b S (PiTensorProduct.map (fun i : S.1 => ev i (x i)) (PiTensorProduct.tprod K w))
    rw [pointwiseEvaluation_pure, PiTensorProduct.map_tprod, pure]
  exact LinearMap.congr_fun h v

/-- The coefficient-valued evaluations on the full product distinguish restricted
tensors when the local evaluations are jointly faithful. -/
theorem pointwiseEvaluation_injective [∀ i, Nonempty (X i)]
    (hsep : ∀ i (f : A i), (∀ x, ev i x f = 0) → f = 0)
    (hb : ∀ i ∉ E, b i ≠ 0) : Function.Injective (pointwiseEvaluation ev E a b href) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  obtain ⟨S, v, rfl⟩ := exists_of E a f
  have hv : v = 0 := by
    refine finiteEvaluation_eq_zero (fun i : S.1 => ev i) (fun i => hsep i) v ?_
    intro y
    let x (i : ι) : X i := if hi : i ∈ S.1 then y ⟨i, hi⟩ else Classical.choice (inferInstance)
    have hxy (i : S.1) : x i = y i := by simp [x, i.2]
    have he := congrFun hf x
    rw [pointwiseEvaluation_of, show (0 : (∀ i, X i) → Space K V E b) x = 0 from rfl] at he
    apply (injective_iff_map_eq_zero _).mp (of_injective E b hb S)
    simpa only [hxy] using he
  rw [hv, map_zero]

end Langlands.RestrictedTensor
