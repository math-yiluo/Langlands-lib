/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit

/-!
# Torsion cohomological dimension of curves and of one-variable function fields

A separated scheme of finite type and dimension at most one over an algebraically closed field
has torsion étale cohomological dimension at most two, and at most one if it is affine
(`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE`, blueprint
`theorem-cohomology-curves`). The same holds over a separably closed field, since the base
change to an algebraic closure is a universal homeomorphism
(`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed`). Consequently the
rational function field `F(x)` in one variable over a separably closed field `F` has torsion
cohomological dimension at most one
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_one_ratFunc`, blueprint
`lemma-uniform-bounds-pro-etale-affines`): `Spec F(x)` is the limit of the nonempty affine opens of
the affine line.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `theorem-cohomology-curves`: The torsion bound on an arbitrary algebraic curve.

Let `X` be a separated scheme of finite type and of dimension at most one over an algebraically
closed field `k` (that is, `X ⟶ Spec k` is an `AlgebraicGeometry.IsCurve`). Then
`cd_tor(X) ≤ 2`, and `cd_tor(X) ≤ 1` if `X` is affine. -/
theorem IsCurve.hasTorsionCohomologicalDimensionLE {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] :
    X.HasTorsionCohomologicalDimensionLE 2 ∧
      (IsAffine X → X.HasTorsionCohomologicalDimensionLE 1) :=
  ⟨fun F hF q hq ↦ subsingleton_sheafH_of_three_le f F hF q hq,
    fun _ F hF q hq ↦ subsingleton_sheafH_of_two_le_of_isAffine f F hF q hq⟩

/-- The torsion bound on a curve over a separably closed field `k`: `cd_tor(X) ≤ 2`, and
`cd_tor(X) ≤ 1` if `X` is affine. The base change `X_k̄ ⟶ X` to an algebraic closure is a
universal homeomorphism, `k̄/k` being purely inseparable, so this follows from
`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE`. -/
theorem IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed {k : Type u} [Field k]
    [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] :
    X.HasTorsionCohomologicalDimensionLE 2 ∧
      (IsAffine X → X.HasTorsionCohomologicalDimensionLE 1) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsCurve (pullback.snd f g) :=
    { krullDim_le_one := by
        rw [IsHomeomorph.topologicalKrullDim_eq _ (pullback.fst f g).isHomeomorph]
        exact IsCurve.krullDim_le_one (f := f) }
  obtain ⟨h₂, h₁⟩ := IsCurve.hasTorsionCohomologicalDimensionLE (pullback.snd f g)
  exact ⟨h₂.of_isUniversalHomeomorphism (pullback.fst f g),
    fun _ ↦ (h₁ inferInstance).of_isUniversalHomeomorphism (pullback.fst f g)⟩

/-- Let `R` be a domain with fraction field `K`. If `cd_tor(Spec Γ(Spec R, U)) ≤ n` for every
nonempty affine open `U` of `Spec R`, then `cd_tor(Spec K) ≤ n`: `Spec K` is the limit of these
affine schemes (`AlgebraicGeometry.Scheme.isLimitFunctionFieldCone`). -/
lemma Scheme.HasTorsionCohomologicalDimensionLE.spec_of_isFractionRing (R : CommRingCat.{u})
    [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
    (h : ∀ U : (Spec R).NonemptyAffineOpens,
      ((Spec R).affineOpensDiagram.obj U).HasTorsionCohomologicalDimensionLE n) :
    (Spec (.of K)).HasTorsionCohomologicalDimensionLE n := by
  have hlim := Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit _
    (Spec R).functionFieldCone (Spec R).isLimitFunctionFieldCone h
  let e : (Spec R).functionField ≃+* K :=
    (IsLocalization.algEquiv (nonZeroDivisors R) (Spec R).functionField K).toRingEquiv
  exact hlim.of_isUniversalHomeomorphism (Spec.map (CommRingCat.ofHom e.symm.toRingHom))

/-- Blueprint `lemma-uniform-bounds-pro-etale-affines`: One-variable fields over a separably closed
field.

If `F` is a separably closed field, then the rational function field `F(x)` has torsion
cohomological dimension at most one: `cd_tor(Spec F(x)) ≤ 1`. Indeed `Spec F(x)` is the limit of
the nonempty affine opens `U` of the affine line over `F`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.spec_of_isFractionRing`), and each
`U` is an affine curve over `F`, so that `cd_tor(U) ≤ 1`
(`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed`). -/
theorem Scheme.hasTorsionCohomologicalDimensionLE_one_ratFunc (F : Type u) [Field F]
    [IsSepClosed F] : (Spec (.of (RatFunc F))).HasTorsionCohomologicalDimensionLE 1 := by
  have : IsDomain (CommRingCat.of (Polynomial F)) := inferInstanceAs (IsDomain (Polynomial F))
  let _ : Algebra (CommRingCat.of (Polynomial F)) (RatFunc F) :=
    inferInstanceAs (Algebra (Polynomial F) (RatFunc F))
  have : IsFractionRing (CommRingCat.of (Polynomial F)) (RatFunc F) :=
    inferInstanceAs (IsFractionRing (Polynomial F) (RatFunc F))
  refine Scheme.HasTorsionCohomologicalDimensionLE.spec_of_isFractionRing
    (CommRingCat.of (Polynomial F)) (RatFunc F) fun U ↦ ?_
  let a : Spec (CommRingCat.of (Polynomial F)) ⟶ Spec (.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F (Polynomial F)))
  have : LocallyOfFiniteType a := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hdim : topologicalKrullDim (Spec (CommRingCat.of (Polynomial F))) ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial F)) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  have : IsCurve (U.2.1.fromSpec ≫ a) :=
    { krullDim_le_one :=
        (U.2.1.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdim }
  exact (IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed (U.2.1.fromSpec ≫ a)).2
    inferInstance

end AlgebraicGeometry
