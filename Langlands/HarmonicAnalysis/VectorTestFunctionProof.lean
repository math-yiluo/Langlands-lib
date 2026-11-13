import Langlands.HarmonicAnalysis.VectorTestFunctionStatements
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Renard II.1.2: vector-valued disjoint indicators and the canonical tensor maps -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators TensorProduct

universe uX uV uA uW

namespace Langlands.HarmonicAnalysis.VectorTestFunctionProof

open VectorTestFunction VectorTestFunctionStatements
open Hecke.TestFunction

section Injectivity

variable {X : Type uX} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A tensor map `A ⊗ V → W` is injective as soon as `A` embeds linearly into
functions `X → ℂ`, `W` maps linearly to functions `X → V`, and pure tensors
go to the pointwise products `x ↦ a(x) • v`. -/
theorem lift_injective_of_pointwise {A : Type uA} [AddCommGroup A] [Module ℂ A]
    {W : Type uW} [AddCommMonoid W] [Module ℂ W]
    (ev : A →ₗ[ℂ] X → ℂ) (hev : Function.Injective ev)
    (E : W →ₗ[ℂ] X → V) (φ : A ⊗[ℂ] V →ₗ[ℂ] W)
    (hφ : ∀ (a : A) (v : V) (x : X), E (φ (a ⊗ₜ[ℂ] v)) x = ev a x • v) :
    Function.Injective φ := by
  classical
  refine (injective_iff_map_eq_zero φ).mpr ?_
  intro t ht
  let b := Module.Basis.ofVectorSpace ℂ V
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b t
  have key (x : X) : ∑ i ∈ c.support, ev (c i) x • b i = 0 := by
    have h := congrFun (congrArg E ht) x
    simpa [Finsupp.sum, map_sum, Finset.sum_apply, hφ] using h
  have hc : c = 0 := by
    ext i
    by_cases hi : i ∈ c.support
    · apply hev
      ext x
      simpa using
        (linearIndependent_iff'.mp b.linearIndependent) c.support
          (fun j => ev (c j) x) (key x) i hi
    · simpa using hi
  simp [hc]

variable [TopologicalSpace X]

/-- Injectivity of the canonical map in (II.1.2.3). -/
theorem smoothTensorMap_injective :
    Function.Injective (smoothTensorMap (X := X) (V := V)) := by
  refine lift_injective_of_pointwise (LocallyConstant.coeFnₗ ℂ)
    DFunLike.coe_injective (LocallyConstant.coeFnₗ ℂ) smoothTensorMap ?_
  intro a v x
  rfl

/-- Injectivity of the canonical map in (II.1.2.4). -/
theorem compactTensorMap_injective :
    Function.Injective (compactTensorMap (X := X) (V := V)) := by
  refine lift_injective_of_pointwise (schwartzBruhatSubmodule X).subtype
    (schwartzBruhatSubmodule X).injective_subtype
    ((LocallyConstant.coeFnₗ ℂ).comp inclusion) compactTensorMap ?_
  intro a v x
  rfl

end Injectivity

section Decomposition

variable {X : Type uX} [TopologicalSpace X] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Pointwise evaluation of a finite sum of vector-valued compact tests. -/
theorem space_sum_apply {ι : Type*} (s : Finset ι) (F : ι → Space X V) (x : X) :
    (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  change ((LocallyConstant.coeFnₗ ℂ).comp (inclusion (X := X) (V := V))
    (∑ i ∈ s, F i)) x = _
  rw [map_sum, Finset.sum_apply]
  rfl

/-- The finitely many nonzero fibers are pairwise disjoint compact clopen sets. -/
theorem disjointIndicatorDecomposition : DisjointIndicatorDecomposition.{uX, uV} := by
  classical
  intro X _ _ _ _ V _ _ f
  have hlc : IsLocallyConstant (f : X → V) := Space.locallyConstant f
  have hcs : HasCompactSupport (f : X → V) := Space.hasCompactSupport f
  let S : Set V := {v | v ∈ Set.range (f : X → V) ∧ v ≠ 0}
  have hS : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport hlc hcs).subset (fun _ hv => hv.1)
  let : Fintype S := hS.fintype
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let U (i : Fin (Fintype.card S)) : Set X := {x | f x = (e i).val}
  have hUo (i) : IsClopen (U i) := hlc.isClopen_fiber (e i).val
  have hUc (i) : IsCompact (U i) :=
    hcs.of_isClosed_subset (hlc.isClosed_fiber (e i).val) (fun x hx => by
      apply subset_tsupport
      change f x ≠ 0
      exact hx ▸ (e i).property.2)
  refine ⟨Fintype.card S, U, hUo, hUc, fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (e.injective (Subtype.ext (hxi.symm.trans hxj)))
  · apply Space.ext
    intro x
    rw [space_sum_apply]
    simp only [compactBilinear_apply, characteristic_apply]
    symm
    by_cases hx : f x = 0
    · have hnot (i) : x ∉ U i := by
        intro hi
        exact (e i).property.2 (hi.symm.trans hx)
      simp [Set.indicator_of_notMem, hnot, hx]
    · let c : S := ⟨f x, ⟨⟨x, rfl⟩, hx⟩⟩
      let i : Fin (Fintype.card S) := e.symm c
      have hei : e i = c := e.apply_symm_apply c
      rw [Finset.sum_eq_single i]
      · have hmem : x ∈ U i := by
          change f x = (e i).val
          rw [hei]
        simp [Set.indicator_of_mem hmem, hei, c]
      · intro j _ hji
        have hnot : x ∉ U j := by
          intro hj
          have hej : e j = c := Subtype.ext hj.symm
          exact hji (e.injective (hej.trans hei.symm))
        simp [Set.indicator_of_notMem hnot]
      · simp

end Decomposition

/-- Surjectivity of (II.1.2.4) from the vector-valued decomposition. -/
theorem compactTensorSurjective : CompactTensorSurjective.{uX, uV} := by
  intro X _ _ _ _ V _ _ f
  obtain ⟨n, U, hUo, hUc, v, -, hf⟩ := disjointIndicatorDecomposition X V f
  refine ⟨∑ i, characteristic (hUo i) (hUc i) ⊗ₜ[ℂ] v i, ?_⟩
  rw [hf, map_sum]
  simp only [compactTensorMap_tmul]

/-- Injectivity of (II.1.2.3), in the exact target form. -/
theorem smoothTensorInjective : SmoothTensorInjective.{uX, uV} := by
  intro X _ _ _ _ V _ _
  exact smoothTensorMap_injective

/-- Injectivity of (II.1.2.4), in the exact target form. -/
theorem compactTensorInjective : CompactTensorInjective.{uX, uV} := by
  intro X _ _ _ _ V _ _
  exact compactTensorMap_injective

/-- The exact unchanged vector-valued indicator and tensor-map target. -/
theorem assertions : Assertions.{uX, uV} :=
  ⟨disjointIndicatorDecomposition, smoothTensorInjective, compactTensorInjective,
    compactTensorSurjective⟩

end Langlands.HarmonicAnalysis.VectorTestFunctionProof
