/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.Order.CompletePartialOrder
import WeilConjectures.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions
import WeilConjectures.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant
import WeilConjectures.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions
import WeilConjectures.AlgebraicGeometry.Curve.ReductionModuleAssertions
import WeilConjectures.AlgebraicGeometry.Curve.DenseIrreducibleOpens
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions
import WeilConjectures.AlgebraicGeometry.Curve.PrimeConstructiblePullback
import WeilConjectures.AlgebraicGeometry.PullbackIsoPrimeTorsionDevissage
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePoints
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.Gabber
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.AlgebraicGeometry.Curve.NormalizationMonoProperties
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-!
# Reduction steps for the eight curve-cohomology assertions

This file collects the reduction steps through which the eight curve-cohomology assertions
`AlgebraicGeometry.IsCurve.Assertions` (and in particular the invariance `C₇` of the cohomology
of a proper curve under extension of algebraically closed fields) are reduced to the
calculations on smooth curves with constant coefficients.

Throughout, `k` is an algebraically closed field, a curve over `k` is a morphism
`f : X ⟶ Spec k` with `AlgebraicGeometry.IsCurve f`, coefficient sheaves are étale sheaves of
`Λ`-modules and `Hᵠ(X, F)` is the cohomology of the underlying abelian sheaf. A sheaf of
`𝐅_r`-modules is a sheaf `F` of `Λ`-modules killed by the prime `r`, i.e. `r • 𝟙 F = 0`, or (in
the hypotheses of the reduction statements) a sheaf of modules over `ULift (ZMod r)`.

## Main statements

- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`: étale cohomology of a
  quasi-compact quasi-separated scheme commutes with filtered colimits.
- `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`: dévissage, the assertions for the outer
  terms of a short exact sequence imply those for the middle term.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`: field
  extension invariance in dimension zero.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`: `C₇` reduces to
  reduced curves and constructible `𝐅_r`-coefficients.
- `AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced`: all eight assertions reduce to
  reduced curves and constructible `𝐅_ℓ`-coefficients.
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek`: localisation to a dense
  open on which the coefficients are finite locally constant.
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek`: the same, split
  along the irreducible components of the dense open.
- `AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`: the normalisation
  exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0`.
- `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite_coefficients`: the
  assertions for `j_! 𝐅_ℓ` on a reduced curve follow from those on its normalisation.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
- Stacks Project, Lemma 59.51.7 (cohomology and filtered colimits),
  <https://stacks.math.columbia.edu/tag/03Q6>
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Dévissage -/

private theorem subsingleton_middle {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (q : ℕ) [Subsingleton (Sheaf.H S.X₁ q)]
    [Subsingleton (Sheaf.H S.X₃ q)] : Subsingleton (Sheaf.H S.X₂ q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ _ hS x
    (Subsingleton.elim _ _)
  change Sheaf.H.map S.f q y = x at hy
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

private theorem finite_middle {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (q : ℕ) [Finite (Sheaf.H S.X₁ q)]
    [Finite (Sheaf.H S.X₃ q)] : Finite (Sheaf.H S.X₂ q) := by
  exact (CategoryTheory.Abelian.Ext.covariant_sequence_exact₂' _ hS q).ab_finite



private theorem surjective_middle_cohomologyMap {X Y : Scheme.{u}} (a : Y ⟶ X)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (q : ℕ) [Subsingleton (Sheaf.H S.X₁ (q + 1))]
    (h₁ : Function.Surjective (Etale.cohomologyMap a S.X₁ q))
    (h₃ : Function.Surjective (Etale.cohomologyMap a S.X₃ q)) :
    Function.Surjective (Etale.cohomologyMap a S.X₂ q) := by
  obtain ⟨hY, δX, δY, _, _, _, _, eX, eY, hf, hg, _⟩ :=
    Etale.pullbackCohomology_longExact_ladder a S hS
  intro y
  obtain ⟨x₃, hx₃⟩ := h₃ (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.g) q y)
  obtain ⟨x, hx⟩ := ((eX q).2.1 x₃).mp (Subsingleton.elim _ _)
  have hz : Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.g) q
      (y - Etale.cohomologyMap a S.X₂ q x) = 0 := by
    rw [map_sub, ← hg q x, hx, hx₃, sub_self]
  obtain ⟨y₁, hy₁⟩ := ((eY q).1 _).mp hz
  obtain ⟨x₁, hx₁⟩ := h₁ y₁
  refine ⟨x + Sheaf.H.map S.f q x₁, ?_⟩
  rw [map_add, hf q x₁, hx₁, hy₁, add_sub_cancel]

private theorem bijective_middle_cohomologyMap {X Y : Scheme.{u}} (a : Y ⟶ X)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (h₁ : ∀ q, Function.Bijective (Etale.cohomologyMap a S.X₁ q))
    (h₃ : ∀ q, Function.Bijective (Etale.cohomologyMap a S.X₃ q)) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap a S.X₂ q) := by
  obtain ⟨hY, δX, δY, _, _, _, hiY, eX, eY, hf, hg, hδ⟩ :=
    Etale.pullbackCohomology_longExact_ladder a S hS
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hgx : Sheaf.H.map S.g q x = 0 := (h₃ q).1 (by
      rw [hg q x, hx, map_zero, map_zero])
    obtain ⟨x₁, hx₁⟩ := ((eX q).1 x).mp hgx
    have hz : Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.f) q
        (Etale.cohomologyMap a S.X₁ q x₁) = 0 := by
      rw [← hf q x₁, hx₁, hx]
    cases q with
    | zero =>
      have hx₁zero : x₁ = 0 := (h₁ 0).1 (hiY (by simpa only [map_zero] using hz))
      rw [← hx₁, hx₁zero, map_zero]
    | succ q =>
      obtain ⟨y₃, hy₃⟩ := ((eY q).2.2 _).mp hz
      obtain ⟨x₃, hx₃⟩ := (h₃ q).2 y₃
      have he : δX q x₃ = x₁ := (h₁ (q + 1)).1 (by
        rw [hδ q x₃, hx₃, hy₃])
      rw [← hx₁, ← he]
      exact (eX q).2.2.apply_apply_eq_zero x₃
  · intro y
    obtain ⟨x₃, hx₃⟩ :=
      (h₃ q).2 (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.g) q y)
    have hz : δX q x₃ = 0 := (h₁ (q + 1)).1 (by
      rw [hδ q x₃, hx₃, (eY q).2.1.apply_apply_eq_zero, map_zero])
    obtain ⟨x, hx⟩ := ((eX q).2.1 x₃).mp hz
    have hgzero : Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.g) q
        (y - Etale.cohomologyMap a S.X₂ q x) = 0 := by
      rw [map_sub, ← hg q x, hx, hx₃, sub_self]
    obtain ⟨y₁, hy₁⟩ := ((eY q).1 _).mp hgzero
    obtain ⟨x₁, hx₁⟩ := (h₁ q).2 y₁
    refine ⟨x + Sheaf.H.map S.f q x₁, ?_⟩
    rw [map_add, hf q x₁, hx₁, hy₁, add_sub_cancel]

private theorem primary_outer {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) (p : ℕ) (hF : Scheme.IsPrimaryTorsionSheaf Λ S.X₂ p) :
    Scheme.IsPrimaryTorsionSheaf Λ S.X₁ p ∧
      Scheme.IsPrimaryTorsionSheaf Λ S.X₃ p := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro Ω _ _ s x
    let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
      (Scheme.pointSmallEtale s).sheafFiber
    have : PreservesFiniteLimits E := inferInstance
    have : PreservesFiniteColimits E := inferInstance
    obtain ⟨n, hn⟩ := hF Ω s (E.map S.f x)
    refine ⟨n, (ModuleCat.mono_iff_injective (E.map S.f)).mp (Functor.map_mono E S.f) ?_⟩
    simpa only [map_nsmul, map_zero] using hn
  · intro Ω _ _ s x
    let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
      (Scheme.pointSmallEtale s).sheafFiber
    have : PreservesFiniteLimits E := inferInstance
    have : PreservesFiniteColimits E := inferInstance
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (E.map S.g)).mp (Functor.map_epi E S.g) x
    obtain ⟨n, hn⟩ := hF Ω s y
    refine ⟨n, ?_⟩
    rw [← map_nsmul, hn, map_zero]

private theorem invertible_outer {X B : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) [Scheme.IsTorsionSheafOfInvertibleOrder B S.X₂] :
    Scheme.IsTorsionSheafOfInvertibleOrder B S.X₁ ∧
      Scheme.IsTorsionSheafOfInvertibleOrder B S.X₃ := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · constructor
    intro Ω _ _ s x
    let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
      (Scheme.pointSmallEtale s).sheafFiber
    have : PreservesFiniteLimits E := inferInstance
    have : PreservesFiniteColimits E := inferInstance
    obtain ⟨n, hn, hu, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := B) Ω s (E.map S.f x)
    refine ⟨n, hn, hu, (ModuleCat.mono_iff_injective (E.map S.f)).mp (Functor.map_mono E S.f) ?_⟩
    simpa only [map_nsmul, map_zero] using hx
  · constructor
    intro Ω _ _ s x
    let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
      (Scheme.pointSmallEtale s).sheafFiber
    have : PreservesFiniteLimits E := inferInstance
    have : PreservesFiniteColimits E := inferInstance
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (E.map S.g)).mp (Functor.map_epi E S.g) x
    obtain ⟨n, hn, hu, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := B) Ω s y
    refine ⟨n, hn, hu, ?_⟩
    rw [← map_nsmul, hx, map_zero]

private theorem constructible_outer {X : Scheme.{u}} [IsNoetherian X]
    [IsNoetherianRing Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) [Scheme.IsConstructibleSheaf S.X₂] :
    Scheme.IsConstructibleSheaf S.X₁ ∧ Scheme.IsConstructibleSheaf S.X₃ := by
  have : Mono S.f := hS.mono_f
  have h₁ : Scheme.IsConstructibleSheaf S.X₁ :=
    Scheme.constructible_of_mono_noetherian S.f
  have : Scheme.IsConstructibleSheaf (cokernel S.f) :=
    Scheme.IsConstructibleSheaf.cokernel S.f
  exact ⟨h₁, Scheme.IsConstructibleSheaf.of_iso (F := cokernel S.f)
    ((cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel)⟩

/-- **Short exact dévissage for the eight curve assertions.** Let `X` be a curve over `k` and
`0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` a short exact sequence of étale sheaves of `Λ`-modules on `X`. If the
eight assertions `C(X, F₁)` and `C(X, F₂)` hold, then so does `C(X, F)`: the long exact
cohomology sequences (and their pullbacks along a field extension) pass vanishing, finiteness
and bijectivity to the middle term, the hypotheses of the assertions being inherited by
subsheaves and quotients, constructibility for subsheaves since `Λ` is noetherian; for `C₈` one uses
`H³(X, F₁) = 0`, i.e. `C₁(X, F₁)`.
(blueprint: theorem-cohomology-curves)
-/
theorem IsCurve.Assertions.of_shortExact [IsNoetherianRing Λ] {k : Type u} [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (h₁ : IsCurve.Assertions Λ f S.X₁) (h₃ : IsCurve.Assertions Λ f S.X₃) :
    IsCurve.Assertions Λ f S.X₂ := by
  let A := S.map (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  have hA : A.ShortExact := Etale.shortExact_map_forget₂ Λ hS
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have : Subsingleton (Sheaf.H A.X₁ q) := h₁.subsingleton_of_two_lt q hq
    have : Subsingleton (Sheaf.H A.X₃ q) := h₃.subsingleton_of_two_lt q hq
    exact subsingleton_middle hA q
  · intro _ q hq
    have : Subsingleton (Sheaf.H A.X₁ q) := h₁.subsingleton_of_one_lt_of_isAffine q hq
    have : Subsingleton (Sheaf.H A.X₃ q) := h₃.subsingleton_of_one_lt_of_isAffine q hq
    exact subsingleton_middle hA q
  · intro p _ _ hp q hq
    obtain ⟨hp₁, hp₃⟩ := primary_outer Λ hS p hp
    have : Subsingleton (Sheaf.H A.X₁ q) :=
      h₁.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hp₁ q hq
    have : Subsingleton (Sheaf.H A.X₃ q) :=
      h₃.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hp₃ q hq
    exact subsingleton_middle hA q
  · intro _ _ q
    obtain ⟨hc₁, hc₃⟩ := constructible_outer Λ hS
    obtain ⟨hi₁, hi₃⟩ := invertible_outer Λ (B := Spec (.of k)) hS
    have : Finite (Sheaf.H A.X₁ q) := h₁.finite_of_isTorsionSheafOfInvertibleOrder q
    have : Finite (Sheaf.H A.X₃ q) := h₃.finite_of_isTorsionSheafOfInvertibleOrder q
    exact finite_middle hA q
  · intro _ _ q
    obtain ⟨hc₁, hc₃⟩ := constructible_outer Λ hS
    have : Finite (Sheaf.H A.X₁ q) := h₁.finite_of_isProper q
    have : Finite (Sheaf.H A.X₃ q) := h₃.finite_of_isProper q
    exact finite_middle hA q
  · intro _ k' _ _ X' ι f' ι' h q
    obtain ⟨hi₁, hi₃⟩ := invertible_outer Λ (B := Spec (.of k)) hS
    exact bijective_middle_cohomologyMap ι' hA
      (fun n ↦ h₁.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h n)
      (fun n ↦ h₃.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h n) q
  · intro _ k' _ _ X' ι f' ι' h q
    exact bijective_middle_cohomologyMap ι' hA
      (fun n ↦ h₁.bijective_cohomologyMap_of_isProper k' h n)
      (fun n ↦ h₃.bijective_cohomologyMap_of_isProper k' h n) q
  · intro W a _
    have : Subsingleton (Sheaf.H A.X₁ 3) := h₁.subsingleton_of_two_lt 3 (by decide)
    exact surjective_middle_cohomologyMap a hA 2
      (h₁.surjective_cohomologyMap_of_isOpenImmersion a)
      (h₃.surjective_cohomologyMap_of_isOpenImmersion a)

/-! ### Dimension zero -/

private theorem subsingleton_sheafH_of_dim_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hC : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H F q) := by
  have h := (zero_dimensional_etale_cohomology k C f hC F
    (fun x ↦ AlgebraicClosure (C.residueField x)) C.algClosurePoint
    (fun x ↦ C.algClosurePoint_base x default)).2.1 q hq
  let e := (Scheme.nonempty_sheafH_extDerivedIso C q).some.app F
  constructor
  intro x y
  exact e.addCommGroupIsoToAddEquiv.injective (h.elim _ _)


/-- **Field extension in dimension zero.** Let `k ⊆ k'` be algebraically closed fields, `C` a
separated `k`-scheme of finite type of dimension at most zero, and `F` a torsion étale sheaf of
`Λ`-modules on `C`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` is bijective for every `q`: both sides vanish for
`q > 0`, and in degree zero both are the finite product of the stalks of `F` at the points of
`C`. (blueprint: `lemma-sheaves-finite-support-finite-morphisms--2`) 
(blueprint: lemma-sheaves-finite-support-finite-morphisms--2)
-/
theorem IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  by
    let A := (sheafCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    cases q with
    | zero =>
      let A' := ((ι')^*[AddCommGrpCat.{u + 1}]).obj A
      let e : Sheaf.H A 0 ≃+ (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
        (Sheaf.H.equiv₀ A terminalIsTerminal).trans
          (((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm.app A)
            |>.addCommGroupIsoToAddEquiv)
      let e' : Sheaf.H A' 0 ≃+
          (Sheaf.Γ C'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A' :=
        (Sheaf.H.equiv₀ A' terminalIsTerminal).trans
          (((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm.app A')
            |>.addCommGroupIsoToAddEquiv)
      have hΓ := Etale.bijective_globalSectionsUpperStarMap_of_dim_zero f hC h A
      have he (x : Sheaf.H A 0) :
          Etale.cohomologyMap ι' A 0 x =
            e'.symm (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' A (e x)) := by
        have hh := Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap ι' A (e x)
        change Etale.cohomologyMap ι' A 0 (e.symm (e x)) =
          e'.symm (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' A (e x)) at hh
        simpa only [AddEquiv.symm_apply_apply] using hh
      have hb := e'.symm.bijective.comp (hΓ.comp e.bijective)
      have heq : Etale.cohomologyMap ι' A 0 =
          e'.symm ∘ Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' A ∘ e :=
        funext he
      change Function.Bijective (Etale.cohomologyMap ι' A 0)
      rw [heq]
      exact hb
    | succ q =>
      obtain ⟨a, rfl⟩ := Spec.map_surjective ι
      let : Algebra k k' := a.hom.toAlgebra
      let : C.Over (Spec (.of k)) := ⟨f⟩
      have : IsSeparated (C ↘ Spec (.of k)) := by
        change IsSeparated f
        infer_instance
      have : LocallyOfFiniteType (C ↘ Spec (.of k)) := by
        change LocallyOfFiniteType f
        infer_instance
      have : QuasiCompact (C ↘ Spec (.of k)) := by
        change QuasiCompact f
        infer_instance
      have hdim := (zeroDimensional_baseChange_points k k' C hC).2.2.2.2.1
      change topologicalKrullDim (pullback f (Spec.map a) : Scheme.{u}) ≤ 0 at hdim
      have hdim' : topologicalKrullDim C' ≤ 0 := by
        rw [IsHomeomorph.topologicalKrullDim_eq h.isoPullback.hom
          h.isoPullback.hom.homeomorph.isHomeomorph]
        exact hdim
      have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
      have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
      have : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
      have := subsingleton_sheafH_of_dim_zero f hC A (q + 1) (Nat.zero_lt_succ q)
      have := subsingleton_sheafH_of_dim_zero f' hdim'
        (((ι')^*[AddCommGrpCat.{u + 1}]).obj A) (q + 1) (Nat.zero_lt_succ q)
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-! ### Reduction to constructible prime torsion -/

/-- **Reduction of `C₇` to constructible prime torsion on reduced curves.** Let `k` be
algebraically closed. Suppose that `C₇` holds for every reduced proper curve `X` over `k`,
every prime `r` and every constructible sheaf `G` of `𝐅_r`-modules on `X` (modules over
`ULift (ZMod r)`), i.e. that the pullback `Hᵠ(X, G) ⟶ Hᵠ(X', ι'^* G)` is bijective for every
base change `X'` of `X` to an algebraically closed extension `k'` of `k`. Then `C₇(C, F)`
holds for every proper curve `C` over `k` and every torsion sheaf `F` of `Λ`-modules.

The proof replaces `C` by `C_red` (a universal homeomorphism), writes the underlying abelian
sheaf of `F` as the filtered colimit of its constructible subsheaves
(`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`), splits a constructible sheaf into
its primary parts and dévisses an `r`-primary one along `0 → F[r] → F → F/F[r] → 0`
(`AlgebraicGeometry.IsCurve.Assertions.of_shortExact`).
(blueprint: theorem-cohomology-curves--7)
-/
theorem IsCurve.bijective_cohomologyMap_of_forall_isReduced {k : Type u} [Field k]
    [IsAlgClosed k]
    (H : ∀ {X X' : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve g] [IsProper g] [IsReduced X]
      (k' : Type u) [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)}
      {g' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (_ : IsPullback ι' g' g ι) (r : ℕ) [Fact r.Prime]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      [Scheme.IsConstructibleSheaf G] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj G) q))
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] (k' : Type u)
    [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')}
    {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  by
    let A := (sheafCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    obtain ⟨hred, hclosed, hsurj, -⟩ :=
      reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism C
    let C₀ := C.nilradical.subscheme
    let i : C₀ ⟶ C := C.nilradical.subschemeι
    have : IsReduced C₀ := hred
    have : IsClosedImmersion i := hclosed
    have : Surjective i := hsurj
    have : IsUniversalHomeomorphism i := inferInstance
    have : IsCurve (i ≫ f) :=
      { toIsSeparated := inferInstance
        toLocallyOfFiniteType := inferInstance
        toQuasiCompact := inferInstance
        krullDim_le_one := by
          rw [IsHomeomorph.topologicalKrullDim_eq i i.isHomeomorph]
          exact IsCurve.krullDim_le_one (f := f) }
    let P := pullback ι' i
    let j : P ⟶ C' := pullback.fst ι' i
    let a : P ⟶ C₀ := pullback.snd ι' i
    have h₀ : IsPullback a (j ≫ f') (i ≫ f) ι :=
      (IsPullback.of_hasPullback ι' i).flip.paste_vert h
    have : IsProper (i ≫ f) := inferInstance
    have : IsProper (j ≫ f') := MorphismProperty.of_isPullback h₀ inferInstance
    have : CompactSpace C₀ := (quasiCompact_iff_compactSpace (i ≫ f)).mp inferInstance
    have : QuasiSeparatedSpace C₀ := quasiSeparatedSpace_of_quasiSeparated (i ≫ f)
    have : CompactSpace P := (quasiCompact_iff_compactSpace (j ≫ f')).mp inferInstance
    have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated (j ≫ f')
    let A₀ := ((i)^*[AddCommGrpCat.{u + 1}]).obj A
    have ht : A.IsTorsion :=
      (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance
    have ht₀ : Scheme.IsTorsionAbelianSheaf A₀ :=
      (Scheme.isTorsionAbelianSheaf_characterizations A₀).1.mpr (Etale.isTorsion_upperStar i ht)
    have ha : Function.Bijective (Etale.cohomologyMap a A₀ q) := by
      apply Etale.pullback_cohomology_bijective_of_prime_torsion_devissage a ?_ A₀ ht₀ q
      intro r hr G hG q
      have : Fact r.Prime := ⟨hr⟩
      apply Etale.bijective_cohomologyMap_of_constructible_prime a r ?_ G hG q
      intro M _ q
      exact H (i ≫ f) k' h₀ r M q
    have hi : Function.Bijective (Etale.cohomologyMap i A q) :=
      Etale.cohomologyMap_bijective i A q
    let e := (Sheaf.functorH P.smallEtaleTopology q).mapIso
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} a i).app A)
    have he : Function.Bijective (Sheaf.H.map
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} a i).hom.app A) q) :=
      e.addCommGroupIsoToAddEquiv.bijective
    have hcomp : Etale.cohomologyMap a A₀ q ∘ Etale.cohomologyMap i A q =
        Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} a i).hom.app A) q ∘
          Etale.cohomologyMap (a ≫ i) A q :=
      funext (Etale.cohomologyPullbackFunctorial a i A q).2.1
    have hai : Function.Bijective (Etale.cohomologyMap (a ≫ i) A q) :=
      (he.of_comp_iff' _).mp (hcomp ▸ ha.comp hi)
    have hw : a ≫ i = j ≫ ι' := (pullback.condition (f := ι') (g := i)).symm
    rw [hw] at hai
    have hj : Function.Bijective
        (Etale.cohomologyMap j (((ι')^*[AddCommGrpCat.{u + 1}]).obj A) q) :=
      Etale.cohomologyMap_bijective j _ q
    let e' := (Sheaf.functorH P.smallEtaleTopology q).mapIso
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} j ι').app A)
    have he' : Function.Bijective (Sheaf.H.map
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} j ι').hom.app A) q) :=
      e'.addCommGroupIsoToAddEquiv.bijective
    have hcomp' :
        Etale.cohomologyMap j (((ι')^*[AddCommGrpCat.{u + 1}]).obj A) q ∘
          Etale.cohomologyMap ι' A q =
        Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} j ι').hom.app A) q ∘
          Etale.cohomologyMap (j ≫ ι') A q :=
      funext (Etale.cohomologyPullbackFunctorial j ι' A q).2.1
    exact (hj.of_comp_iff' _).mp (hcomp'.symm ▸ he'.comp hai)

/-- **Constructible and primary reduction of the eight assertions.** Let `k` be algebraically
closed. Suppose that the eight assertions `C(X, G)` hold for every reduced curve `X` over `k`,
every prime `ℓ` and every constructible sheaf `G` of `𝐅_ℓ`-modules on `X` (modules over
`ULift (ZMod ℓ)`). Then `C(C, F)` holds for every curve `C` over `k` and every torsion sheaf
`F` of `Λ`-modules, for a finite ring `Λ` (over an infinite ring such as `𝐅_ℓ[t]` the constant
sheaf is constructible and its `H⁰` on a proper curve is infinite); in particular so does the field
extension invariance `C₇`.

The proof is that of `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`,
run for all eight assertions simultaneously: reduction to `C_red`, constructible approximation
and continuity of cohomology, primary decomposition, and induction on the exponent along
`0 → F[ℓ] → F → F/F[ℓ] → 0` using `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`.
(blueprint: theorem-cohomology-curves)
-/
theorem IsCurve.Assertions.of_forall_isReduced [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k]
    (H : ∀ {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve g] [IsReduced X] (ℓ : ℕ)
      [Fact ℓ.Prime]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions (ULift.{u + 1} (ZMod ℓ)) g G)
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] :
    IsCurve.Assertions Λ f F :=
  by
    obtain ⟨hred, hclosed, hsurj, -⟩ :=
      reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism C
    let C₀ := C.nilradical.subscheme
    let i : C₀ ⟶ C := C.nilradical.subschemeι
    have : IsReduced C₀ := hred
    have : IsClosedImmersion i := hclosed
    have : Surjective i := hsurj
    have : IsCurve (i ≫ f) :=
      { toIsSeparated := inferInstance
        toLocallyOfFiniteType := inferInstance
        toQuasiCompact := inferInstance
        krullDim_le_one := by
          rw [IsHomeomorph.topologicalKrullDim_eq i i.isHomeomorph]
          exact IsCurve.krullDim_le_one (f := f) }
    let F₀ := ((i)^*[ModuleCat.{u + 1} Λ]).obj F
    have hconstructible : ∀ (G : Sheaf C₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [Scheme.IsConstructibleSheaf G], IsCurve.Assertions Λ (i ≫ f) G := by
      intro G _
      apply IsCurve.assertions_of_constructible_prime_devissage Λ (i ≫ f) ?_ G
      intro r _ M _
      exact H (i ≫ f) r M
    have hF₀ : IsCurve.Assertions Λ (i ≫ f) F₀ :=
      IsCurve.assertions_of_constructible_approximation Λ (i ≫ f) hconstructible F₀
    exact IsCurve.assertions_of_reduction Λ f F hF₀

/-! ### Localisation to a dense open -/

/-- **Dense-open localisation reduction.** Let `X` be a reduced curve over an algebraically
closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime `r`, over a
finite ring `Λ`. There is a dense open `j : U ⟶ X` whose connected components are irreducible
and on which `F` is finite locally constant, and for it the eight assertions for `F` are
equivalent to those for `j_! j^* F`: the open–closed sequence `0 → j_! j^* F → F → i_* i^* F → 0`
has third term
supported on the zero-dimensional complement `Z` of `U`, whose cohomology is concentrated in
degree zero and invariant under field extension.
(blueprint: theorem-cohomology-curves)
-/
theorem IsCurve.exists_dense_assertions_iff_lowerShriek [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      (∀ x ∈ (U : Set X), IsIrreducible (connectedComponentIn (U : Set X) x)) ∧
      Scheme.IsFiniteLocallyConstantSheaf ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F) ∧
      (IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
        ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  by
    obtain ⟨V, hV, hFV⟩ := Scheme.IsConstructibleSheaf.exists_dense_open F
    obtain ⟨n, U, hUV, hU, -, -, -, hcomp⟩ :=
      IsCurve.exists_dense_irreducible_opens f V hV
    let W : X.Opens := ⨆ a, U a
    have hW : Dense (W : Set X) := by
      simpa only [W, TopologicalSpace.Opens.coe_iSup] using hU
    have hWV : W ≤ V := iSup_le hUV
    have hFW : Scheme.IsFiniteLocallyConstantSheaf
        ((W.ι)^*[ModuleCat.{u + 1} Λ].obj F) := by
      have := hFV
      apply Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset W.ι V.ι
      simpa only [Scheme.Opens.range_ι] using (show (W : Set X) ⊆ V from hWV)
    refine ⟨W, hW, ?_, hFW, ?_⟩
    · simpa only [W, TopologicalSpace.Opens.coe_iSup] using hcomp
    · exact IsCurve.assertions_iff_dense_open_prime Λ f r F hF W hW

/-- **Dense-open localisation, componentwise.** Let `C` be a reduced curve over an
algebraically closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime
`r`, over a finite ring `Λ`. There are finitely many pairwise disjoint irreducible opens
`U_a ⊆ C`, with dense union `U` and zero-dimensional complement `Z = C ∖ U`, on each of which
`F` is finite locally constant, such that, writing `j_a : U_a ⟶ C` for the inclusions,
`C(C, F) ↔ ∀ a, C(C, j_{a,!}(F|_{U_a}))`. This combines the open–closed sequence
`0 → j_! j^* F → F → i_* i^* F → 0`, the assertions on the zero-dimensional `Z`, the
decomposition `j_! j^* F = ⨁_a j_{a,!}(F|_{U_a})` and dévissage.
(blueprint: theorem-cohomology-curves)
-/
theorem IsCurve.exists_dense_assertions_iff_forall_lowerShriek [Finite Λ] {k : Type u}
    [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    (r : ℕ) [Fact r.Prime] (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ (n : ℕ) (U : Fin n → C.Opens), Dense (⋃ a, (U a : Set C)) ∧
      Pairwise (fun a b ↦ Disjoint (U a : Set C) (U b)) ∧ (∀ a, IsIrreducible (U a : Set C)) ∧
      topologicalKrullDim ↥(⋃ a, (U a : Set C))ᶜ ≤ 0 ∧
      (∀ a, Scheme.IsFiniteLocallyConstantSheaf (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ∧
      (IsCurve.Assertions Λ f F ↔ ∀ a, IsCurve.Assertions Λ f
        (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  by
    obtain ⟨V, hV, hFV⟩ := Scheme.IsConstructibleSheaf.exists_dense_open F
    obtain ⟨n, U, hUV, hU, hdisj, hirr, hdim, -⟩ :=
      IsCurve.exists_dense_irreducible_opens f V hV
    have hW : Dense ((⨆ a, U a : C.Opens) : Set C) := by
      simpa only [TopologicalSpace.Opens.coe_iSup] using hU
    refine ⟨n, U, hU, hdisj, hirr, hdim, ?_, ?_⟩
    · intro a
      have := hFV
      apply Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (U a).ι V.ι
      simpa only [Scheme.Opens.range_ι] using
        (show (U a : Set C) ⊆ V from hUV a)
    · exact (IsCurve.assertions_iff_dense_open_prime Λ f r F hF (⨆ a, U a) hW).trans
        (IsCurve.assertions_iff_disjoint_open_prime Λ f r F hF n U hdisj)

/-! ### Normalisation -/

/-- **The normalisation exact sequence.** Let `X` be a reduced curve over an algebraically
closed field `k`, `ν : X' ⟶ X` a finite surjective morphism which is an isomorphism over a
dense open `V ⊆ X` (e.g. the normalisation of `X`), `j : U ⟶ X` an open immersion and
`j' : U' ⟶ X'` its pullback along `ν`. For a prime `ℓ` with `Λ/ℓΛ` finite there is a
monomorphism

`α : j_! (Λ/ℓ)_U ⟶ ν_* j'_! (Λ/ℓ)_{U'}`

(the extension by zero of the unit of `ν|_{U'}^* ⊣ ν|_{U'*}`, stalkwise the diagonal into the
fibre) whose cokernel `Q` is constructible and supported on the finite set `X ∖ V`, giving the
short exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0`.

Mathlib's `Scheme.Hom.normalization` is the relative normalisation of a morphism, and does not
directly provide the normalisation of a reduced curve together with its finiteness; we therefore
state the lemma for an arbitrary finite surjective `ν` which is an isomorphism over a dense open,
the properties of the normalisation that are used. The compatibility of the sequence with field
extension and restriction to opens, also part of the blueprint statement, is not recorded in
this existential form. (blueprint: `lemma-normalization-constant-sheaf--1`) 
(blueprint: lemma-normalization-constant-sheaf--1)
-/
theorem exists_mono_lowerShriek_constantModSheaf_lowerStar {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] (V : X.Opens) (hV : Dense (V : Set X))
    [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'} [IsOpenImmersion j']
    {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] :
    ∃ α : (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)),
      Mono α ∧ Scheme.IsConstructibleSheaf (cokernel α) ∧
        IsZero ((V.ι)^*[ModuleCat.{u + 1} Λ].obj (cokernel α)) :=
  by
    have : Surjective ν' := MorphismProperty.of_isPullback hj inferInstance
    let M : ModuleCat.{u + 1} Λ := ModuleCat.of Λ (Λ ⧸ Ideal.span {(ℓ : Λ)})
    let e := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) ν').app M
    let η := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν').unit.app
      (Etale.constantModSheaf Λ U ℓ)
    have : Mono η := Etale.mono_unit_app_of_surjective Λ ν' ν'.surjective _
    let β : (j)_!open[ModuleCat.{u + 1} Λ].obj
        ((ν')_*[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)) :=
      (Etale.finiteOpenComparison (ModuleCat.{u + 1} Λ) hj).app
        (Etale.constantModSheaf Λ U' ℓ)
    let α : (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)) :=
      (j)_!open[ModuleCat.{u + 1} Λ].map
        (η ≫ (ν')_*[ModuleCat.{u + 1} Λ].map e.hom) ≫ β
    have : IsIso β := Etale.isIso_finiteOpenComparison_app (ModuleCat.{u + 1} Λ) hj _
    have : PreservesFiniteLimits (j)_!open[ModuleCat.{u + 1} Λ] := inferInstance
    have : IsIso ((ν')_*[ModuleCat.{u + 1} Λ].map e.hom) := inferInstance
    have : IsIso ((j)_!open[ModuleCat.{u + 1} Λ].map
        ((ν')_*[ModuleCat.{u + 1} Λ].map e.hom)) := inferInstance
    have hm₁ : Mono ((j)_!open[ModuleCat.{u + 1} Λ].map η) := Functor.map_mono _ η
    have hm₂ : Mono ((j)_!open[ModuleCat.{u + 1} Λ].map
        ((ν')_*[ModuleCat.{u + 1} Λ].map e.hom)) := inferInstance
    have hm₃ : Mono β := by
      constructor
      intro Z a b h
      have h' := congrArg (fun m ↦ m ≫ inv β) h
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h'
    have hα : Mono α := by
      dsimp only [α]
      rw [Functor.map_comp]
      exact mono_comp' (mono_comp' hm₁ hm₂) hm₃
    exact ⟨α, hα, normalization_mono_properties (Λ := Λ) f ν V hV j hj ℓ α hα⟩

/-- **Normalisation and the smooth constant case.** Let `X` be a reduced curve over an
algebraically closed field `k`, `ν : X' ⟶ X` a finite surjective morphism from a smooth
`k`-scheme which is an isomorphism over a dense open (e.g. the normalisation of `X`),
`j : U ⟶ X` an open immersion and `j' : U' ⟶ X'` its pullback along `ν`. Then the eight
assertions for `j_! 𝐅_ℓ` on `X` follow from those for `j'_! 𝐅_ℓ` on the smooth curve `X'`
(which are the Kummer and Artin–Schreier calculations): finite direct image is exact and
preserves cohomology, and the normalisation exact sequence
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar` has a third term whose
cohomology is concentrated in degree zero and invariant under field extension.
(blueprint: theorem-cohomology-curves)
-/
theorem IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite_coefficients {k : Type u}
  [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] [Smooth (ν ≫ f)] (V : X.Opens)
    (hV : Dense (V : Set X)) [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j]
    {j' : U' ⟶ X'} [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime] [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]
    (H : IsCurve.Assertions Λ (ν ≫ f)
      ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))) :
    IsCurve.Assertions Λ f ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)) :=
  by
    obtain ⟨α, hα, hQ, hQV⟩ :=
      exists_mono_lowerShriek_constantModSheaf_lowerStar Λ f ν V hV j hj ℓ
    let F' := (j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)
    let G := (ν)_*[ModuleCat.{u + 1} Λ].obj F'
    have : Mono α := hα
    have : Scheme.IsConstructibleSheaf (cokernel α) := hQ
    have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
    have : Scheme.IsConstructibleSheaf G :=
      finite_pushforward_open_constantModSheaf_constructible Λ ν j' ℓ
    have Hν : IsCurve.Assertions Λ f G :=
      IsCurve.Assertions.of_finite_pushforward_module Λ ν f F' H
    have hconst : ℓ • 𝟙 (Etale.constantModSheaf Λ U' ℓ) = 0 := by
      rw [Etale.constantModSheaf, ← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
        ← (constantSheaf _ _).map_zero]
      congr 1
      ext
      simpa using (Ideal.Quotient.eq_zero_iff_mem).2
        (Ideal.mem_span_singleton_self (ℓ : Λ))
    have hF' : ℓ • 𝟙 F' = 0 := by
      change ℓ • 𝟙 ((j')_!open[ModuleCat.{u + 1} Λ].obj
        (Etale.constantModSheaf Λ U' ℓ)) = 0
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hconst, Functor.map_zero]
    have hG : ℓ • 𝟙 G = 0 := by
      change ℓ • 𝟙 ((ν)_*[ModuleCat.{u + 1} Λ].obj F') = 0
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hF', Functor.map_zero]
    exact IsCurve.Assertions.of_finite_support_mono Λ f α ℓ hG V hV hQV Hν

end AlgebraicGeometry
