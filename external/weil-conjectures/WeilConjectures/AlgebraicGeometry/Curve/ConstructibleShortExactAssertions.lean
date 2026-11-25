/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.SixFunctors.Etale.Gabber
import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-! # Short-exact devissage with constructible outer terms

Source: Stacks Project, Lemma 0A5C. The proof specializes the existing proof in
Curve.Reductions; this standalone module avoids its import of ConstructiblePrimeDevissage.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Short exact dévissage for the eight curve assertions.** Let `X` be a curve over `k` and
`0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` a short exact sequence of étale sheaves of `Λ`-modules on `X`. If the
eight assertions `C(X, F₁)` and `C(X, F₂)` hold, then so does `C(X, F)`: the long exact
cohomology sequences (and their pullbacks along a field extension) pass vanishing, finiteness
and bijectivity to the middle term, the hypotheses of the assertions being inherited by
subsheaves and quotients; constructibility of the outer terms is assumed; for `C₈` one uses
`H³(X, F₁) = 0`, i.e. `C₁(X, F₁)`.
(blueprint: lem-v2-constructible-short-exact-assertions) -/
theorem IsCurve.Assertions.of_constructible_shortExact {k : Type u} [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [Scheme.IsConstructibleSheaf S.X₁] [Scheme.IsConstructibleSheaf S.X₃]
    (h₁ : IsCurve.Assertions Λ f S.X₁) (h₃ : IsCurve.Assertions Λ f S.X₃) :
    IsCurve.Assertions Λ f S.X₂ := by
  have subsingleton_middle {X : Scheme.{u}}
      {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
      (hS : S.ShortExact) (q : ℕ) [Subsingleton (Sheaf.H S.X₁ q)]
      [Subsingleton (Sheaf.H S.X₃ q)] : Subsingleton (Sheaf.H S.X₂ q) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ _ hS x
      (Subsingleton.elim _ _)
    change Sheaf.H.map S.f q y = x at hy
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  have finite_middle {X : Scheme.{u}}
      {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
      (hS : S.ShortExact) (q : ℕ) [Finite (Sheaf.H S.X₁ q)]
      [Finite (Sheaf.H S.X₃ q)] : Finite (Sheaf.H S.X₂ q) := by
    exact (CategoryTheory.Abelian.Ext.covariant_sequence_exact₂' _ hS q).ab_finite
  have surjective_middle_cohomologyMap {X Y : Scheme.{u}} (a : Y ⟶ X)
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
  have bijective_middle_cohomologyMap {X Y : Scheme.{u}} (a : Y ⟶ X)
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
  have primary_outer (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
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
  have invertible_outer (Λ : Type (u + 1)) [CommRing Λ] {X B : Scheme.{u}}
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
  let A := S.map (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  have hA : A.ShortExact := Etale.shortExact_map_forget₂ Λ hS
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
    obtain ⟨hi₁, hi₃⟩ := invertible_outer Λ (B := Spec (.of k)) hS
    have : Finite (Sheaf.H A.X₁ q) := h₁.finite_of_isTorsionSheafOfInvertibleOrder q
    have : Finite (Sheaf.H A.X₃ q) := h₃.finite_of_isTorsionSheafOfInvertibleOrder q
    exact finite_middle hA q
  · intro _ _ q
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

end AlgebraicGeometry
