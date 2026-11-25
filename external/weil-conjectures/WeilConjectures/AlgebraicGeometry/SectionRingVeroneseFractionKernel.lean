/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionMap
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition

/-! # The kernel of the explicit map on Veronese numerator sections

Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

private def rel (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (tr : ∀ n b : ℕ, M n →ₗ[R] M (n + b)) : Submodule R (⨁ n, M n) :=
  Submodule.span R {z | ∃ n b t, z = of M n t - of M (n + b) (tr n b t)}

private theorem rel_normal (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (tr : ∀ n b : ℕ, M n →ₗ[R] M (n + b)) (z : ⨁ n, M n) :
    ∃ n t, z - of M n t ∈ rel R M tr := by
  classical
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | of n t => exact ⟨n, t, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, t, ht⟩ := hx
    obtain ⟨m, u, hu⟩ := hy
    have htn : of M n t - of M (n + m) (tr n m t) ∈ rel R M tr :=
      Submodule.subset_span ⟨n, m, t, rfl⟩
    have hun : of M m u - of M (m + n) (tr m n u) ∈ rel R M tr :=
      Submodule.subset_span ⟨m, n, u, rfl⟩
    have hy' : ∃ u' : M (m + n), y - of M (m + n) u' ∈ rel R M tr :=
      ⟨tr m n u, by simpa only [sub_add_sub_cancel] using Submodule.add_mem _ hu hun⟩
    rw [Nat.add_comm m n] at hy'
    obtain ⟨u', hu'⟩ := hy'
    refine ⟨n + m, tr n m t + u', ?_⟩
    have hx' : x - of M (n + m) (tr n m t) ∈ rel R M tr := by
      simpa only [sub_add_sub_cancel] using Submodule.add_mem _ ht htn
    simpa only [map_add, add_sub_add_comm] using Submodule.add_mem _ hx' hu'

private theorem kernel_rel (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (tr : ∀ n b : ℕ, M n →ₗ[R] M (n + b)) {G : Type*} [AddCommGroup G] (f : (⨁ n, M n) →+ G)
    (htr : ∀ n b t, f (of M n t) = f (of M (n + b) (tr n b t)))
    (hkill : ∀ n t, f (of M n t) = 0 → ∃ b, tr n b t = 0) :
    (rel R M tr).toAddSubgroup = f.ker := by
  have hforward : (rel R M tr).toAddSubgroup ≤ f.ker := by
    intro z hz
    change z ∈ Submodule.span R _ at hz
    have hz' : ∀ r : R, f (r • z) = 0 := by
      induction hz using Submodule.span_induction with
      | mem x hx =>
        rintro r
        obtain ⟨n, b, t, rfl⟩ := hx
        rw [smul_sub, ← DirectSum.of_smul, ← DirectSum.of_smul,
          ← LinearMap.map_smul, map_sub, htr, sub_self]
      | zero => intro r; simp
      | add x y hx hy ihx ihy =>
        intro r
        rw [smul_add, map_add, ihx, ihy, zero_add]
      | smul a x hx ih =>
        intro r
        rw [smul_smul]
        exact ih (r * a)
    change f z = 0
    simpa only [one_smul] using hz' 1
  apply le_antisymm hforward
  intro z hz
  obtain ⟨n, t, ht⟩ := rel_normal R M tr z
  have hft : f (of M n t) = 0 := by
    have h := hforward ht
    change f (z - of M n t) = 0 at h
    change f z = 0 at hz
    rw [map_sub, hz, zero_sub, neg_eq_zero] at h
    exact h
  obtain ⟨b, hb⟩ := hkill n t hft
  have hmem : of M n t ∈ rel R M tr := by
    have h : of M n t - of M (n + b) (tr n b t) ∈ rel R M tr :=
      Submodule.subset_span ⟨n, b, t, rfl⟩
    simpa only [hb, map_zero, sub_zero] using h
  change z ∈ rel R M tr
  simpa only [sub_add_cancel] using Submodule.add_mem _ ht hmem

private theorem loc_transition {A : Type*} [CommRing A] (s a : A) (n b : ℕ) :
    Localization.mk a (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s) =
      (Localization.mk (a * s ^ b) ⟨s ^ (n + b), ⟨n + b, rfl⟩⟩ :
        Localization (Submonoid.powers s)) := by
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp only [pow_add]
  ring

private theorem loc_kill {A : Type*} [CommRing A] (s a : A) (n : ℕ)
    (h : Localization.mk a (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s) =
      (0 : Localization (Submonoid.powers s))) : ∃ b, a * s ^ b = 0 := by
  rw [Localization.mk_eq_mk'] at h
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h
  obtain ⟨b, hb⟩ := c.property
  refine ⟨b, ?_⟩
  simpa only [← hb, mul_comm] using hc

/-- The transition relations are exactly the kernel of the explicitly constructed fraction map.
Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
(blueprint: lem-sc-section-ring-veronese-fraction-kernel)

Proof: write `T_n` for `sectionRingVeroneseNumeratorIso` on global sections and `ι_n`
for the direct-sum injection in the numerator presentation. The inverse identification
sends a section `t` to the homogeneous ring element `a_n(t) = of_(nd)(T_n⁻¹(t))`.
Tensor-power coherence gives
`a_(n+b)(mulTensorPowSection(s) n b t) = a_n(t) * s^b`.
To check this equality, restrict to an open set trivializing the invertible module `L`.
In the chosen generator, `T_n` identifies the generator to its `nd`-th tensor power,
the section-ring product multiplies the coefficient functions, and the transition
multiplies the coefficient by the `b`-th power of the coefficient of `s`. Both sides
are therefore the same function times the same generator. Equality of sections glues
from these opens. The same calculation shows that scalar multiplication by a global
function corresponds to multiplication by its degree-zero image in the section ring.

Consequently every transition difference
`ι_n(t) - ι_(n+b)(mulTensorPowSection(s) n b t)` maps to zero: its two images are
`a_n(t)/s^n` and `(a_n(t)*s^b)/s^(n+b)`. Every global-function scalar multiple also
maps to zero by the scalar calculation. Additivity now proves that the entire submodule
span of the transition differences lies in the additive kernel.

Conversely take a finite sum `z = sum_n ι_n(t_n)` in the kernel, with finite support `I`.
Choose `N` at least every index in `I`. Subtract, for each index `n`, the defining relation
with `b = N-n`. Modulo the relation submodule, `z` is thus the single generator `ι_N(t)`,
where `t` is the sum of the transitioned numerators. Its image is `a_N(t)/s^N = 0`.
The localization equality criterion supplies a natural number `k` with
`s^k * a_N(t) = 0`. By the coherence equality and injectivity of the direct-sum injection
and of `T_(N+k)⁻¹`, the transition of `t` from degree `N` to degree `N+k` is zero.
The relation with indices `N,k` then says that `ι_N(t)` belongs to the relation submodule.
Adding back the previously subtracted relations shows that `z` belongs to it as well.
An empty support gives `z=0` immediately. This proves the reverse kernel inclusion.

The argument uses powers and finite supports only: `d=0` is allowed, and if `s` is
zero or nilpotent the localization criterion still supplies a killing power; the same
transition makes every numerator class zero. No reducedness or nonzero-divisor
hypothesis is used. This is a kernel computation for a fixed explicit map, not an
existence statement about an unspecified equivalence.
-/
theorem sectionRingVeroneseFractionMap_kernel
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup =
      (sectionRingVeroneseFractionMap X L d s).ker := by
  let M : ℕ → Type u := fun n ↦ Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)
  let tr : ∀ n b : ℕ, M n →ₗ[Γ(X, ⊤)] M (n + b) := fun n b ↦
    { toAddHom := ((mulTensorPowSection
        (homOfGlobalSection (L.tensorPow d) (s.val d)) (𝟙_ X.Modules) n b).app ⊤).hom
      map_smul' := fun r t ↦ Hom.app_smul _ r t }
  let f := sectionRingVeroneseFractionMap X L d s
  have hval (n : ℕ) (t : M n) :
      (f (DirectSum.of M n t)).val =
        Localization.mk (sectionRingVeroneseNumerator X L d n t).val
          (⟨s.val ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s.val) := by
    simp only [f, sectionRingVeroneseFractionMap]
    change Localization.mk _ _ = _
    have ht : (DirectSum.of M n t) n = t := by
      apply DirectSum.of_eq_same
    rw [ht]
    simp
  have htr (n b : ℕ) (t : M n) :
      f (DirectSum.of M n t) = f (DirectSum.of M (n + b) (tr n b t)) := by
    apply HomogeneousLocalization.val_injective
    rw [hval, hval]
    change _ = Localization.mk
      (sectionRingVeroneseNumerator X L d (n + b)
        ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
          (𝟙_ X.Modules) n b).app ⊤ t)).val _
    rw [sectionRingVeroneseNumerator_transition]
    exact loc_transition s.val _ n b
  have hkill (n : ℕ) (t : M n) (ht : f (DirectSum.of M n t) = 0) :
      ∃ b, tr n b t = 0 := by
    have ht' := congrArg HomogeneousLocalization.val ht
    rw [hval, HomogeneousLocalization.val_zero] at ht'
    obtain ⟨b, hb⟩ := loc_kill s.val _ n ht'
    refine ⟨b, ?_⟩
    have hinj : Function.Injective (sectionRingVeroneseNumerator X L d (n + b)) := by
      classical
      intro a c hac
      have hac' := congrArg Subtype.val hac
      change DirectSum.of (SectionRingComponent L) ((n + b) • d)
        ((sectionRingVeroneseNumeratorIso X L d (n + b)).inv.app ⊤ a) =
          DirectSum.of (SectionRingComponent L) ((n + b) • d)
            ((sectionRingVeroneseNumeratorIso X L d (n + b)).inv.app ⊤ c) at hac'
      have hi := DirectSum.of_injective (β := SectionRingComponent L) ((n + b) • d) hac'
      exact (ConcreteCategory.bijective_of_isIso
        ((sectionRingVeroneseNumeratorIso X L d (n + b)).inv.app ⊤)).1 hi
    apply hinj
    apply Subtype.ext
    change (sectionRingVeroneseNumerator X L d (n + b)
      ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
        (𝟙_ X.Modules) n b).app ⊤ t)).val =
          (sectionRingVeroneseNumerator X L d (n + b) 0).val
    rw [sectionRingVeroneseNumerator_transition, hb, map_zero]
    rfl
  classical
  exact kernel_rel Γ(X, ⊤) M tr f htr hkill

end AlgebraicGeometry.Scheme.Modules
