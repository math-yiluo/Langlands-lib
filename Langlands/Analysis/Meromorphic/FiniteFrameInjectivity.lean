import Langlands.Analysis.Meromorphic.FiniteDimensionalValues
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Topology.Instances.Matrix

/-! # Injectivity of weakly holomorphic finite frames

For an operator family with finite-dimensional domain, nonvanishing of a determinant of
continuous scalar tests suffices to ensure injectivity. If the continuous dual of the
codomain separates points, such a determinant exists at every injective parameter.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Filter Set Topology
open scoped Manifold

section Retraction

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [SeparatingDual ℂ V] {n : ℕ}

/-- Finite-dimensional injections into a space with separating dual admit continuous
linear left inverses. Use finite-dimensional retraction in the space of all functions on the
continuous dual, and restrict it along the continuous map of evaluations. -/
theorem exists_finiteFrameLeftInverse (L : (Fin n → ℂ) →L[ℂ] V) (hL : Function.Injective L) :
    ∃ Q : V →L[ℂ] (Fin n → ℂ), Function.LeftInverse Q L := by
  classical
  let ev : V →L[ℂ] ((V →L[ℂ] ℂ) → ℂ) := .pi fun f => f
  have hev : Function.Injective ev := fun x y h =>
    (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr (congrFun h)
  let L' := ev.comp L
  let b := Pi.basisFun ℂ (Fin n)
  have hb : LinearIndependent ℂ (fun j => L' (b j)) :=
    b.linearIndependent.map' L'.toLinearMap (LinearMap.ker_eq_bot.mpr (hev.comp hL))
  obtain ⟨Q, hQ⟩ := exists_continuousLinearMap_leftInverse _ hb
  refine ⟨Q.comp ev, fun x => ?_⟩
  change Q (L' x) = x
  have hx : ∑ j, x j • b j = x := by
    simpa only [b, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using b.sum_equivFun x
  rw [← hx, map_sum]
  simp_rw [map_smul]
  exact (hQ x).trans hx.symm

/-- A chosen continuous linear retraction of an injective finite frame. -/
def finiteFrameLeftInverse (L : (Fin n → ℂ) →L[ℂ] V) (hL : Function.Injective L) :
    V →L[ℂ] (Fin n → ℂ) := (exists_finiteFrameLeftInverse L hL).choose

@[simp]
theorem finiteFrameLeftInverse_apply (L : (Fin n → ℂ) →L[ℂ] V) (hL : Function.Injective L)
    (x : Fin n → ℂ) : finiteFrameLeftInverse L hL (L x) = x :=
  (exists_finiteFrameLeftInverse L hL).choose_spec x

end Retraction

section Families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V W B : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
  {U : Set M}

/-- A finite combination of fixed postcompositions of a weakly holomorphic operator family,
with holomorphic scalar coefficients, is still weakly holomorphic. -/
theorem IsHolomorphicOperatorFamilyOn.sum_smul_comp [IsTopologicalAddGroup W]
    [ContinuousConstSMul ℂ W] {A : M → B →L[ℂ] V} (hA : IsHolomorphicOperatorFamilyOn I A U)
    {κ : Type*} [Fintype κ] (L : κ → V →L[ℂ] W) (c : κ → M → ℂ)
    (hc : ∀ j, MDifferentiableOn I 𝓘(ℂ, ℂ) (c j) U) :
    IsHolomorphicOperatorFamilyOn I (fun s => ∑ j, c j s • (L j ∘L A s)) U := by
  intro x φ
  have h := MDifferentiableOn.sum (t := Finset.univ) (fun j _ =>
    (hc j).mul (hA x (φ.comp (L j))))
  refine h.congr fun s _ => ?_
  simp only [Finset.sum_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    map_sum, map_smul, smul_eq_mul, Pi.mul_apply]

/-- A weakly holomorphic family of finite frames is injective near each point of injectivity,
relative to the set on which it is weakly holomorphic. -/
theorem IsHolomorphicOperatorFamilyOn.eventually_injective [SeparatingDual ℂ V]
    {n : ℕ} {A : M → (Fin n → ℂ) →L[ℂ] V} (hA : IsHolomorphicOperatorFamilyOn I A U)
    {s₀ : M} (hs₀ : s₀ ∈ U) (hinj : Function.Injective (A s₀)) :
    ∀ᶠ s in 𝓝[U] s₀, Function.Injective (A s) := by
  let Q := finiteFrameLeftInverse (A s₀) hinj
  let m : M → Matrix (Fin n) (Fin n) ℂ := fun s =>
    LinearMap.toMatrix' (Q.comp (A s)).toLinearMap
  have hm₀ : m s₀ = 1 := by
    have heq : (Q.comp (A s₀)).toLinearMap = LinearMap.id := by
      ext x
      exact congrFun (finiteFrameLeftInverse_apply (A s₀) hinj _) _
    simp only [m, heq, LinearMap.toMatrix'_id]
  have hm : ContinuousWithinAt m U s₀ := by
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    simpa only [m, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      ((hA (Pi.single j 1) ((ContinuousLinearMap.proj i).comp Q)) s₀ hs₀).continuousWithinAt
  have hd : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ => p.det) := continuous_id.matrix_det
  have hd₀ : (m s₀).det ≠ 0 := by simp [hm₀]
  have hev : ∀ᶠ s in 𝓝[U] s₀, (m s).det ≠ 0 :=
    (hd.continuousAt.tendsto.comp hm).eventually (eventually_ne_nhds hd₀)
  filter_upwards [hev] with s hs x y hxy
  apply Matrix.mulVec_injective_of_det_ne_zero hs
  simpa only [m, LinearMap.toMatrix'_mulVec, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply] using congrArg Q hxy

/-- A range cover by a weakly holomorphic operator family that is injective at one parameter
is a finite-type witness on an open neighbourhood of that parameter. -/
theorem IsHolomorphicOperatorFamilyOn.exists_open_finiteTypeOn [SeparatingDual ℂ V]
    {n : ℕ} {A : M → (Fin n → ℂ) →L[ℂ] V} (hA : IsHolomorphicOperatorFamilyOn I A U)
    {S : M → Set V} (hS : ∀ s ∈ U, S s ⊆ Set.range (A s))
    (hU : IsOpen U) {s₀ : M} (hs₀ : s₀ ∈ U) (hinj : Function.Injective (A s₀)) :
    ∃ O ⊆ U, IsOpen O ∧ s₀ ∈ O ∧ IsFiniteTypeOn I S O := by
  have h := hA.eventually_injective hs₀ hinj
  rw [hU.nhdsWithin_eq hs₀] at h
  obtain ⟨O, hO, hOo, hsO⟩ := mem_nhds_iff.mp h
  refine ⟨O ∩ U, inter_subset_right, hOo.inter hU, ⟨hsO, hs₀⟩, n, A, ?_, ?_, ?_⟩
  · exact fun x φ => (hA x φ).mono inter_subset_right
  · exact fun s hs => hO hs.1
  · exact fun s hs => hS s hs.2

end Families

end Langlands.Analysis.Meromorphic
