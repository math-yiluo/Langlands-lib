import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Conditional cancellation for vector and operator numerators -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped NNReal CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

universe u uG uI uV uW uJ

namespace UnramifiedOperatorFamily

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {J : Type uJ}
  {U : Set (unramifiedCharacters ν)}

/-- Continuity under a supplied family of scalar linear tests. Separation of
points by the tests is a separate premise. -/
def IsWeaklyContinuousOn (tests : J → W →ₗ[ℂ] ℂ) (f : U → W) : Prop :=
  ∀ j, Continuous (fun χ => tests j (f χ))

theorem isPolynomialOn_scalar_iff (f : U → ℂ) :
    IsPolynomialOn U f ↔
      ∃ a : unramifiedRegularFunctions ν, ∀ χ : U, f χ = a.val χ.val := by
  classical
  constructor
  · rintro ⟨n, b, v, hf⟩
    refine ⟨∑ i, v i • b i, ?_⟩
    intro χ
    rw [hf]
    change _ = (unramifiedRegularFunctions ν).val (∑ i, v i • b i) χ.val
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i hi => mul_comm _ _)
  · rintro ⟨a, ha⟩
    refine ⟨1, fun _ => a, fun _ => 1, ?_⟩
    intro χ
    simpa using ha χ

/-- Polynomiality descends through an injective linear map, using an
algebraic linear left inverse. No topology on either carrier is needed. -/
theorem isPolynomialOn_of_linearMap_injective
    (T : V →ₗ[ℂ] W) (hT : Function.Injective T) (f : U → V)
    (hf : IsPolynomialOn U (fun χ => T (f χ))) :
    IsPolynomialOn U f := by
  have hi (v : V) : T.leftInverse (T v) = v :=
    T.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hT) v
  simpa only [hi] using hf.linearMap T.leftInverse

end UnramifiedOperatorFamily

section ActualCancellation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)
  (hdiv : RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u})

include hp hG hdiv

open UnramifiedOperatorFamily

/-- A continuous vector family with a finite regular numerator admits the
same cancelled denominator as every scalar family. -/
theorem rationalUnramified_cancel_vector_numerator
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W]
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0)
    (f : U → W) (hf : Continuous f)
    (hpoly : IsPolynomialOn U (fun χ => b.val χ.val • f χ)) :
    IsPolynomialOn U (fun χ =>
      (rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb).val χ.val • f χ) := by
  classical
  obtain ⟨n, a, v, ha⟩ := hpoly
  change ∀ χ : U, b.val χ.val • f χ = ∑ i, (a i).val χ.val • v i at ha
  let S : Submodule ℂ W := Submodule.span ℂ (Set.range v)
  let := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hv (i : Fin n) : v i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have hnum (χ : U) : b.val χ.val • f χ ∈ S := by
    rw [ha χ]
    exact S.sum_mem (fun i hi => S.smul_mem _ (hv i))
  have hmem : ∀ χ : U, f χ ∈ S := by
    have hclosed : IsClosed {χ : U | f χ ∈ S} :=
      S.closed_of_finiteDimensional.preimage hf
    have hsub : {χ : U | b.val χ.val ≠ 0} ⊆ {χ : U | f χ ∈ S} := by
      intro χ hbχ
      exact (S.smul_mem_iff hbχ).mp (hnum χ)
    intro χ
    exact closure_minimal hsub hclosed
      (rationalUnramifiedRegular_dense_nonzero_on_open G hp hG b hb hU χ)
  let g : U → S := fun χ => ⟨f χ, hmem χ⟩
  have hg : Continuous g := hf.subtype_mk hmem
  have hpolyS : IsPolynomialOn U (fun χ => b.val χ.val • g χ) := by
    refine ⟨n, a, fun i => ⟨v i, hv i⟩, ?_⟩
    intro χ
    apply Subtype.ext
    simpa only [Submodule.coe_smul, Submodule.coe_sum] using ha χ
  let e := Module.finBasis ℂ S
  have hcoord (i : Fin (Module.finrank ℂ S)) :
      ∃ c : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
        ∀ χ : U,
          (rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb).val χ.val *
            e.repr (g χ) i = c.val χ.val := by
    obtain ⟨a', ha'⟩ := (isPolynomialOn_scalar_iff _).mp
      (hpolyS.linearMap (e.coord i))
    apply rationalUnramifiedCancelledDenominator_numerator G hp hG hdiv hU b hb
      (fun χ => e.repr (g χ) i)
      ((e.coord i).continuous_of_finiteDimensional.comp hg) a'
    intro χ
    simpa only [map_smul, smul_eq_mul, Module.Basis.coord_apply] using ha' χ
  choose c hc using hcoord
  refine ⟨Module.finrank ℂ S, c, fun i => (e i).val, ?_⟩
  intro χ
  have he := congrArg (fun s : S => s.val)
    (e.sum_repr
      ((rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb).val χ.val • g χ))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  refine he.symm.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using hc i χ

/-- Point-separating scalar tests suffice. The product of the scalar target
spaces supplies a Hausdorff topological vector space for the preceding result. -/
theorem rationalUnramified_cancel_weak_vector_numerator
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {J : Type uJ}
    (tests : J → W →ₗ[ℂ] ℂ)
    (hsep : ∀ x y : W, (∀ j, tests j x = tests j y) → x = y)
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0)
    (f : U → W) (hf : IsWeaklyContinuousOn tests f)
    (hpoly : IsPolynomialOn U (fun χ => b.val χ.val • f χ)) :
    IsPolynomialOn U (fun χ =>
      (rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb).val χ.val • f χ) := by
  let T : W →ₗ[ℂ] (J → ℂ) := LinearMap.pi tests
  have hT : Function.Injective T :=
    fun x y he => hsep x y (fun j => congrFun he j)
  apply isPolynomialOn_of_linearMap_injective T hT
  have hpolyT : IsPolynomialOn U (fun χ => b.val χ.val • T (f χ)) := by
    simpa only [map_smul] using hpoly.linearMap T
  have hfT : Continuous (fun χ => T (f χ)) := continuous_pi hf
  simpa only [map_smul] using
    rationalUnramified_cancel_vector_numerator G hp hG hdiv hU b hb
      (fun χ => T (f χ)) hfT hpolyT

/-- A common nonzero algebraic denominator and weak continuity give the
existing whole-region rationality predicate, conditional on local divisibility. -/
theorem rationalUnramified_isRationalOperatorOn_of_weak_continuity
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {J : Type uJ}
    (tests : J → W →ₗ[ℂ] ℂ)
    (hsep : ∀ x y : W, (∀ j, tests j x = tests j y) → x = y)
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U)
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0)
    (A : U → V →ₗ[ℂ] W)
    (hcont : ∀ v, IsWeaklyContinuousOn tests (fun χ => A χ v))
    (hpoly : IsPolynomialOperatorOn U (fun χ => b.val χ.val • A χ)) :
    IsRationalOperatorOn U A := by
  refine ⟨rationalUnramifiedCancelledDenominator G hp hG hdiv hU b hb, ?_, ?_⟩
  · exact rationalUnramifiedCancelledDenominator_eval_ne_zero G hp hG hdiv hU b hb
  · intro v
    exact rationalUnramified_cancel_weak_vector_numerator G hp hG hdiv tests hsep hU b hb
      (fun χ => A χ v) (hcont v) (hpoly v)

end ActualCancellation

end Langlands.Plancherel
