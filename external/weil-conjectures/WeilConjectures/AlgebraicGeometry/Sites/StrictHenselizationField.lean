/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Unramified.Field
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal

/-!
# The strict henselization of a field

Let `K` be a field and `Ω` a separably closed field, algebraic over `K`, viewed as a geometric
point `s : Spec Ω ⟶ Spec K`. The strict henselization `𝒪^{sh}_{Spec K, s}` is a field: the
evaluation `𝒪^{sh}_{Spec K, s} ⟶ Ω` is injective
(`AlgebraicGeometry.Scheme.strictHenselizationEval_injective_of_field`), since the rings of the
pointed étale neighbourhoods are finite products of fields. Its image contains the separable
closure of `K` in `Ω` (`AlgebraicGeometry.Scheme.exists_strictHenselizationEval_eq_of_isSeparable`)
so that `Ω` is purely inseparable over it, and `Spec Ω ⟶ Spec K_(s)` is a universal
homeomorphism (`AlgebraicGeometry.Scheme.isUniversalHomeomorphism_spec_strictHenselizationEval`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry.Scheme

variable {K Ω : Type u} [Field K] [Field Ω] [IsSepClosed Ω] [Algebra K Ω]

/-- The trivial pointed étale neighbourhood `Spec K` of the geometric point
`Spec Ω ⟶ Spec K`. -/
noncomputable def SpecPointedEtaleNeighborhood.baseOfField :
    SpecPointedEtaleNeighborhood (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) where
  R := CommRingCat.of K
  hom := 𝟙 _
  etale := inferInstance
  pt := CommRingCat.ofHom (algebraMap K Ω)
  w := Category.comp_id _

/-- Every element of `Ω` which is separable over `K` is the value of an element of the strict
henselization of `Spec K` at `Spec Ω ⟶ Spec K`: the standard étale algebra of its minimal
polynomial is a pointed étale neighbourhood carrying a root with this value. -/
lemma exists_strictHenselizationEval_eq_of_isSeparable {x : Ω} (hx : IsSeparable K x) :
    ∃ a, strictHenselizationEval (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) a = x := by
  let N := SpecPointedEtaleNeighborhood.baseOfField (K := K) (Ω := Ω)
  let P : StandardEtalePair K :=
    ⟨minpoly K x, minpoly.monic hx.isIntegral, derivative (minpoly K x), 1, 0, 1, by simp⟩
  obtain ⟨N', -, t, -, -, -, ht⟩ := N.exists_standardEtale P x
    ((Polynomial.eval_map _ _).trans (minpoly.aeval K x))
    ((Polynomial.eval_map _ _).trans_ne
      (hx.aeval_derivative_ne_zero (minpoly.aeval K x)))
  exact ⟨N'.ι t, by rw [SpecPointedEtaleNeighborhood.strictHenselizationEval_ι, ht]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation of the strict henselization of `Spec K` at the geometric point
`Spec Ω ⟶ Spec K` is injective. An element `c` of the ring `R` of a pointed étale
neighbourhood with value zero is killed by an element `g` with nonzero value, `R` being a
reduced artinian ring; and `g` becomes a unit on the neighbourhood `Spec R[1/g]`. -/
theorem strictHenselizationEval_injective_of_field :
    Function.Injective
      (strictHenselizationEval (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 1 (fun _ ↦ a)
  obtain ⟨c, rfl⟩ := hN 0
  rw [SpecPointedEtaleNeighborhood.strictHenselizationEval_ι] at ha
  -- the ring of the neighbourhood is an étale `K`-algebra
  let φ : CommRingCat.of K ⟶ N.R := Spec.preimage N.hom
  have hφ : Spec.map φ = N.hom := Spec.map_preimage _
  let := φ.hom.toAlgebra
  have : Algebra.Etale K N.R := by
    have h := N.etale
    rw [← hφ, HasRingHomProperty.Spec_iff (P := @Etale)] at h
    exact RingHom.etale_algebraMap.1 h
  have : Module.Finite K N.R := Algebra.FormallyUnramified.finite_of_free K N.R
  have : _root_.IsReduced N.R := Algebra.FormallyUnramified.isReduced_of_field K N.R
  have : IsArtinianRing N.R := IsArtinianRing.of_finite K N.R
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd c (1 : N.R)
  rw [smul_eq_mul, smul_eq_mul, mul_one] at hy
  let g : N.R := 1 - c * y
  have hcg : c * g = 0 := by
    refine IsReduced.eq_zero _ ⟨n + 1, ?_⟩
    have h0 : c ^ n * g = 0 := by
      simp only [g]
      rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]
    calc (c * g) ^ (n + 1) = (c ^ n * g) * (c * g ^ n) := by ring_nf
      _ = 0 := by rw [h0, zero_mul]
  have hg : N.pt g ≠ 0 := by simp [g, ha]
  obtain ⟨N', u, t, hu, ht, htu, -⟩ := N.exists_standardEtale
    ⟨X - C g, monic_X_sub_C g, X, X, 0, 1, by simp⟩ (N.pt g) (by simp) (by simpa using hg)
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X,
    eval_C, sub_eq_zero] at ht
  rw [Polynomial.map_X, eval_X, ht] at htu
  have huc : u c = 0 := by
    have h := congrArg u.hom hcg
    rw [map_mul, map_zero] at h
    exact (htu.mul_left_eq_zero).1 h
  rw [← hu, CommRingCat.comp_apply, huc, map_zero]

/-- The strict henselization of `Spec K` at a geometric point `Spec Ω ⟶ Spec K` is a field: it
is local with maximal ideal the kernel of the (injective) evaluation. -/
theorem isField_strictHenselization_of_field :
    IsField (strictHenselization (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, maximalIdeal_strictHenselization,
    RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  exact strictHenselizationEval_injective_of_field (ha.trans (map_zero _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- If `Ω` is separably closed and algebraic over `K`, the morphism `Spec Ω ⟶ Spec K_(s)` from
the geometric point `s : Spec Ω ⟶ Spec K` to the strict localization is a universal
homeomorphism: the strict henselization is a field over which `Ω` is purely inseparable. -/
theorem isUniversalHomeomorphism_spec_strictHenselizationEval [Algebra.IsAlgebraic K Ω] :
    IsUniversalHomeomorphism
      (Spec.map (strictHenselizationEval (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))) := by
  set s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let R := ↑(strictHenselization s)
  let _ : Field R := (isField_strictHenselization_of_field (K := K) (Ω := Ω)).toField
  let _ : Algebra R Ω := (strictHenselizationEval s).hom.toAlgebra
  let q := ringExpChar K
  have : ExpChar K q := ringExpChar.expChar K
  have : ExpChar (SpecPointedEtaleNeighborhood.baseOfField (K := K) (Ω := Ω)).R q :=
    inferInstanceAs (ExpChar K q)
  have : ExpChar Ω q := expChar_of_injective_algebraMap (algebraMap K Ω).injective q
  have : ExpChar R q :=
    let ι : K →+* R := (SpecPointedEtaleNeighborhood.baseOfField (K := K) (Ω := Ω)).ι.hom
    expChar_of_injective_ringHom ι.injective q
  have : IsPurelyInseparable R Ω := by
    rw [isPurelyInseparable_iff_pow_mem R q]
    intro x
    have : ExpChar (separableClosure K Ω) q :=
      expChar_of_injective_algebraMap (algebraMap K (separableClosure K Ω)).injective q
    obtain ⟨n, ⟨y, hy⟩⟩ := (isPurelyInseparable_iff_pow_mem (separableClosure K Ω) q).1
      inferInstance x
    obtain ⟨a, ha⟩ := exists_strictHenselizationEval_eq_of_isSeparable (K := K) y.2
    exact ⟨n, a, ha.trans hy⟩
  exact (Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable R Ω).isUniversalHomeomorphism

end AlgebraicGeometry.Scheme
