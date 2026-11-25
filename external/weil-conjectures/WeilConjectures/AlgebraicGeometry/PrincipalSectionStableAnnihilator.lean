/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Uniform annihilator bounds for a principal section

Source: Stacks Project, Tag 01YB, second paragraph, with Tags 01PO and 01Y8.
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

private theorem ring_stable_annihilator
    (A : Type*) [CommRing A] [IsNoetherianRing A] (g : A) :
    ∃ c : ℕ, ∀ (k : ℕ) (s : A), g ^ k * s = 0 → g ^ c * s = 0 := by
  let K : ℕ →o Submodule A A :=
    { toFun := fun k ↦ (LinearMap.mulLeft A (g ^ k)).ker
      monotone' := by
        intro k l h s hs
        change g ^ k * s = 0 at hs
        change g ^ l * s = 0
        rw [← Nat.sub_add_cancel h, pow_add, mul_assoc, hs, mul_zero] }
  obtain ⟨c, hc⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨c, ?_⟩
  intro k s hs
  by_cases h : c ≤ k
  · have hk : s ∈ K k := hs
    rw [← hc k h] at hk
    exact hk
  · have h : k ≤ c := by omega
    exact K.monotone h hs

private theorem stable_annihilator_localization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (g : A) (c : ℕ)
    (hc : ∀ (k : ℕ) (s : A), g ^ k * s = 0 → g ^ c * s = 0)
    (k : ℕ) (s : B) (hs : (algebraMap A B g) ^ k * s = 0) :
    (algebraMap A B g) ^ c * s = 0 := by
  obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj M s
  have hz : algebraMap A B (g ^ k * a) = algebraMap A B 0 := by
    rw [map_mul, map_pow, ← hd, ← mul_assoc, hs, zero_mul, map_zero]
  obtain ⟨e, he⟩ := IsLocalization.exists_of_eq (M := M) hz
  have he' : g ^ k * (e * a) = 0 := by
    simpa only [mul_zero, mul_comm, mul_left_comm, mul_assoc] using he
  have hzero := congrArg (algebraMap A B) (hc k (e * a) he')
  simp only [map_zero, map_mul, map_pow] at hzero
  have hzero' : algebraMap A B e * ((algebraMap A B g) ^ c * s *
      algebraMap A B d) = 0 := by
    rw [← hd] at hzero
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hzero
  have hcancel : (algebraMap A B g) ^ c * s * algebraMap A B d = 0 := by
    apply (IsLocalization.map_units B e).mul_left_cancel
    simpa only [mul_zero] using hzero'
  apply (IsLocalization.map_units B d).mul_right_cancel
  simpa only [zero_mul] using hcancel

/-- A fixed power of a section kills all local power torsion on a Noetherian scheme.

Source: Stacks Project, Tag 01YB, second paragraph (stabilization of ideal-power
annihilators), using Tags 01PO and 01Y8.
(blueprint: lem-sbc-principal-section-stable-annihilator)

Proof: On each affine open the ascending annihilator ideals of powers of g
stabilize, since its ring is Noetherian. A finite affine cover supplies a
common exponent c. Localization is exact and commutes with kernels of
multiplication, so every g-power torsion section on a basic subopen of one
of these affine opens is killed by g^c. For an arbitrary open V, restrict
a section killed by g^k to this basic-open cover of V. Each restriction
is killed by g^c. Sheaf separatedness makes g^c times the original section
zero. This also covers k<c, since Ann(g^k) is contained in Ann(g^c).
For g=0 one may take c=1; for a unit take c=0. The empty scheme is covered
by the empty family, on which separatedness supplies the assertion. -/
theorem exists_principal_section_stable_annihilator
    (X : Scheme.{u}) [IsNoetherian X] (g : Γ(X, ⊤)) :
    ∃ c : ℕ, ∀ (V : X.Opens) (k : ℕ) (s : Γ(X, V)),
      (X.presheaf.map (homOfLE le_top).op g) ^ k * s = 0 →
      (X.presheaf.map (homOfLE le_top).op g) ^ c * s = 0 := by
  classical
  obtain ⟨S, hS, hfin, hcov⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact
      (U := ⊤) (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  let U : S → X.affineOpens := fun i ↦ ⟨i.1, hS i.2⟩
  have hU : (⨆ i, (U i).1) = ⊤ := by
    change (⨆ i : S, i.1) = ⊤
    rw [← sSup_eq_iSup' S]
    exact hcov.symm
  have : Finite S := hfin.to_subtype
  let _ := Fintype.ofFinite S
  have hring (i : S) : IsNoetherianRing Γ(X, (U i).1) :=
    IsLocallyNoetherian.component_noetherian (U i)
  choose d hd using fun i : S ↦ ring_stable_annihilator Γ(X, (U i).1)
    (X.presheaf.map (homOfLE le_top).op g)
  let c := Finset.univ.sup d
  have hbound (i : S) : d i ≤ c := Finset.le_sup (Finset.mem_univ i)
  have hstable (i : S) (k : ℕ) (s : Γ(X, (U i).1))
      (hs : (X.presheaf.map (homOfLE le_top).op g) ^ k * s = 0) :
      (X.presheaf.map (homOfLE le_top).op g) ^ c * s = 0 := by
    rw [← Nat.sub_add_cancel (hbound i), pow_add, mul_assoc, hd i k s hs, mul_zero]
  have hres (A B : X.Opens) (h : A ≤ B) :
      X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE le_top).op g) =
      X.presheaf.map (homOfLE le_top).op g := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  refine ⟨c, ?_⟩
  intro V k s hs
  apply X.IsSheaf.section_ext
  intro x hx
  have hxU : x ∈ ⨆ i, (U i).1 := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  obtain ⟨f, hDV, hxD⟩ := (U i).2.exists_basicOpen_le ⟨x, hx⟩ hxi
  let D := X.basicOpen f
  let sD : Γ(X, D) := X.presheaf.map (homOfLE hDV).op s
  have hzero : (X.presheaf.map (homOfLE le_top).op g) ^ k * sD = 0 := by
    have he := congrArg (X.presheaf.map (homOfLE hDV).op) hs
    simpa only [map_mul, map_pow, map_zero, hres] using he
  have : IsLocalization.Away f Γ(X, D) := (U i).2.isLocalization_basicOpen f
  have hzero' : (X.presheaf.map (homOfLE le_top).op g) ^ c * sD = 0 := by
    have he := stable_annihilator_localization (Submonoid.powers f)
      (X.presheaf.map (homOfLE le_top).op g) c (hstable i) k sD
    have halg : algebraMap Γ(X, (U i).1) Γ(X, D) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := rfl
    rw [halg] at he
    change (X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      (X.presheaf.map (homOfLE le_top).op g)) ^ k * sD = 0 →
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (X.presheaf.map (homOfLE le_top).op g)) ^ c * sD = 0 at he
    rw [hres] at he
    exact he hzero
  refine ⟨D, hDV, hxD, ?_⟩
  simpa only [map_mul, map_pow, map_zero, hres] using hzero'

end AlgebraicGeometry.Scheme
