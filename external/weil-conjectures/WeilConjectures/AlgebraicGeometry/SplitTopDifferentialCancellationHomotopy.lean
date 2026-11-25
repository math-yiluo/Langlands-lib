/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Split top differential and canonical truncation

Source: Stacks Project, Tags 068V and 00MT, explicit split cancellation.
(blueprint: lem-pc-split-top-differential-cancellation-homotopy)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical truncation at a split top differential preserves homotopy type.

Source: Stacks Project, Tags 068V and 00MT, split identity-pair cancellation.
(blueprint: lem-pc-split-top-differential-cancellation-homotopy).

Proof: Write δ for the differential from m to m+1 and σ for a section of δ.
The canonical truncation has cycles (the kernel of δ) in degree m, the original
terms below m, and zero above m. The map id - δ ≫ σ factors uniquely through
cycles. Together with identities below m and zero maps above m, this defines a
chain map r from B to its truncation. The consecutive-differential equation
proves the chain-map identity entering degree m; the kernel equation proves the
one leaving it. The canonical inclusion i satisfies i ≫ r = id. The family
with σ in degree m+1 to m and zero elsewhere is a homotopy between r ≫ i and id:
in degree m its boundary is δ ≫ σ, in degree m+1 it is σ ≫ δ = id, and in all
other degrees it vanishes. Terms above m+1 are zero by the support assumption.
Transport these equations through the canonical term isomorphisms of truncLE
and assemble HomotopyEquiv. This works also for m=0 and for zero terms. -/
theorem split_top_differential_cancellation_homotopy
    (S : Scheme.{u}) (B : CochainComplex S.Modules ℤ) (m : ℕ)
    (hBle : B.IsStrictlyLE (m + 1 : ℕ))
    (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) :
    Nonempty (HomotopyEquiv (B.truncLE m) B) := by
  classical
  let := hBle
  let := hsplit
  let δ := B.d (m : ℤ) (m + 1 : ℕ)
  let σ := section_ δ
  let h : ∀ i j : ℤ, B.X i ⟶ B.X j := fun i j ↦
    if hi : i = (m + 1 : ℕ) then
      if hj : j = (m : ℤ) then
        eqToHom (congrArg B.X hi) ≫ σ ≫ eqToHom (congrArg B.X hj.symm)
      else 0
    else 0
  have hz : ∀ i j, ¬(ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp [h]
    split_ifs with hi hj
    · subst i j
      exact False.elim (hij (by change (m : ℤ) + 1 = (m + 1 : ℕ); omega))
    · rfl
    · rfl
  let N := Homotopy.nullHomotopicMap h
  have hN (i : ℤ) : N.f i =
      B.d i (i + 1) ≫ h (i + 1) i + h i (i - 1) ≫ B.d (i - 1) i := by
    exact Homotopy.nullHomotopicMap_f
      (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)
      (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl) h
  let p : B ⟶ B := 𝟙 B - N
  have hp_high (i : ℤ) (hi : (m : ℤ) < i) : p.f i = 0 := by
    by_cases heq : i = (m + 1 : ℕ)
    · subst i
      simp [p, hN, h, σ, δ]
    · exact (B.isZero_of_isStrictlyLE (m + 1 : ℕ) i (by omega)).eq_of_src _ _
  have hp_on : B.ιTruncLE m ≫ p = B.ιTruncLE m := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i ≤ (m : ℤ)
    · by_cases heq : i = (m : ℤ)
      · subst i
        have h₁ : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by omega
        have h₂ : (m : ℤ) ≠ ((m + 1 : ℕ) : ℤ) := by omega
        simp only [HomologicalComplex.comp_f, p, HomologicalComplex.sub_f_apply,
          Preadditive.comp_sub, Category.comp_id, hN]
        simp only [h, h₁, h₂, dite_true, dite_false, eqToHom_refl,
          Category.id_comp, Category.comp_id, zero_comp, add_zero]
        have hzero : (B.ιTruncLE m).f (m : ℤ) ≫ B.d (m : ℤ) ((m : ℤ) + 1) = 0 := by
          rw [(B.ιTruncLE m).comm (m : ℤ) ((m : ℤ) + 1)]
          have hd : (B.truncLE m).d (m : ℤ) ((m : ℤ) + 1) = 0 :=
            ((B.truncLE m).isZero_of_isStrictlyLE m ((m : ℤ) + 1)
              (by omega)).eq_of_tgt _ _
          rw [hd, zero_comp]
        rw [← Category.assoc, hzero, zero_comp, sub_zero]
      · have h₁ : i + 1 ≠ ((m + 1 : ℕ) : ℤ) := by omega
        have h₂ : i ≠ ((m + 1 : ℕ) : ℤ) := by omega
        simp only [HomologicalComplex.comp_f, p, HomologicalComplex.sub_f_apply,
          HomologicalComplex.id_f, hN]
        have hh₁ : h (i + 1) i = 0 := by simp only [h, dite_eq_right h₁]
        have hh₂ : h i (i - 1) = 0 := by simp only [h, dite_eq_right h₂]
        simp only [hh₁, hh₂, comp_zero, zero_comp, add_zero, sub_zero,
          Category.comp_id]
    · exact ((B.truncLE m).isZero_of_isStrictlyLE m i (by omega)).eq_of_src _ _
  let I := Abelian.image p
  let e : B ⟶ I := Abelian.factorThruImage p
  let j : I ⟶ B := Abelian.image.ι p
  have he_j : e ≫ j = p := Abelian.image.fac p
  have hI : I.IsStrictlyLE m := by
    apply (I.isStrictlyLE_iff m).2
    intro i hi
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi (e.f i)).1
    apply (cancel_mono (j.f i)).1
    simpa only [Category.id_comp, Category.comp_id, comp_zero, zero_comp,
      ← HomologicalComplex.comp_f, he_j] using hp_high i hi
  let := hI
  let g : B ⟶ B.truncLE m := e ≫ inv (I.ιTruncLE m) ≫ CochainComplex.truncLEMap j m
  have hg : g ≫ B.ιTruncLE m = p := by
    dsimp [g]
    rw [Category.assoc, Category.assoc, CochainComplex.ιTruncLE_naturality]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.comp_id, he_j]
  have : Mono (B.ιTruncLE m) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE B (ComplexShape.embeddingUpIntLE m)))
  have hfg : B.ιTruncLE m ≫ g = 𝟙 _ := by
    apply (cancel_mono (B.ιTruncLE m)).1
    rw [Category.assoc, hg, hp_on, Category.id_comp]
  have hNp : Homotopy N 0 := Homotopy.nullHomotopy h hz
  have hp : Homotopy p (𝟙 B) := by
    have hneg : Homotopy (-N) 0 := by
      simpa using hNp.smul (-1 : ℤ)
    simpa only [p, sub_eq_add_neg, add_zero] using (Homotopy.refl (𝟙 B)).add hneg
  exact ⟨⟨B.ιTruncLE m, g, Homotopy.ofEq hfg, (Homotopy.ofEq hg).trans hp⟩⟩

end AlgebraicGeometry.Scheme.Modules
