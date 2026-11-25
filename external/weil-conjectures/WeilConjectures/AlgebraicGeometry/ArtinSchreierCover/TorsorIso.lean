/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.GeometricPoints
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.LinearAlgebra.Lagrange

/-! # The Artin–Schreier cover is a torsor

The map `∐_{a ∈ 𝔽_p} Y ⟶ Y ×_S Y`, `(a, y) ↦ (y + a, y)`, is an isomorphism for the
Artin–Schreier cover `Y ⟶ S`: the difference `d = T₁ - T₂` of the two coordinates on
`Y ×_S Y` satisfies `d ^ p = d`, and the Lagrange idempotents at `d` split `Y ×_S Y` into the
loci `d = a`, each of which is the image of the summand indexed by `a`.
Source: blueprint, lemma-artin-schreier-character-sheaf, steps (4)-(5).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{u}} {f : Γ(S, ⊤)} {P : Polynomial Γ(S, ⊤)}

/-- Every ring map out of `𝔽_p` sends `a` to the cast of its representative. -/
lemma ringHom_zmod_apply {A : Type*} [CommRing A] (g : ZMod p →+* A) (a : ZMod p) :
    g a = (a.val : A) := by
  rw [← map_natCast g, ZMod.natCast_zmod_val]

/-- **The Artin–Schreier cover is a torsor.** The map `∐_{a ∈ 𝔽_p} Y ⟶ Y ×_S Y` whose
`a`-th component is `(y + a, y)` is an isomorphism. -/
theorem isIso_artinSchreier_sigmaDesc (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) :
    IsIso (Sigma.desc fun m : ULift.{u + 1} (ZMod p) ↦
      pullback.lift (f := (adjoinRootCover S P).hom) (g := (adjoinRootCover S P).hom)
        (artinSchreierTranslation hP hchar m.down) (𝟙 _) (by simp)) := by
  classical
  set π := (adjoinRootCover S P).hom
  set T := adjoinRootCoverRoot S P
  let F := fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left
  set D := Sigma.desc fun m : ULift.{u + 1} (ZMod p) ↦
      pullback.lift (f := π) (g := π) (artinSchreierTranslation hP hchar m.down) (𝟙 _)
        (by simp [π])
  let W := pullback π π
  have hW : (p : Γ(W, ⊤)) = 0 := natCast_appTop_eq_zero hchar (pullback.fst π π ≫ π)
  let ψ : ZMod p →+* Γ(W, ⊤) := zmodRingHomOfNatCastEqZero p hW
  let d : Γ(W, ⊤) := (pullback.fst π π).appTop T - (pullback.snd π π).appTop T
  have hd : d ^ Fintype.card (ZMod p) = d := by
    refine FiniteField.sub_pow_card_eq_of_pow_card_sub_eq ψ ?_
    rw [ZMod.card, appTop_adjoinRootCoverRoot_pow_sub hP, appTop_adjoinRootCoverRoot_pow_sub hP,
      pullback.condition]
  let E (m : ULift.{u + 1} (ZMod p)) : Γ(W, ⊤) := FiniteField.lagrangeAt ψ d m.down
  have hι (m : ULift.{u + 1} (ZMod p)) : Sigma.ι F m ≫ D =
      pullback.lift (f := π) (g := π) (artinSchreierTranslation hP hchar m.down) (𝟙 _)
        (by simp [π]) := Sigma.ι_comp_desc _ _
  have key (m : ULift.{u + 1} (ZMod p)) :
      IsOpenImmersion (Sigma.ι F m ≫ D) ∧ Set.range (Sigma.ι F m ≫ D) = W.basicOpen (E m) := by
    refine isOpenImmersion_and_range_eq_of_section (pullback.snd π π) _
      (by rw [hι, pullback.lift_snd]) _ ?_ ?_
    · rw [Scheme.preimage_basicOpen_top, FiniteField.map_lagrangeAt]
      refine (congrArg _ ?_).trans (Scheme.basicOpen_one _)
      have hd' : (Sigma.ι F m ≫ D).appTop d =
          ((Sigma.ι F m ≫ D).appTop.hom.comp ψ) m.down := by
        rw [ringHom_zmod_apply, map_sub, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
          ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hι, pullback.lift_fst,
          pullback.lift_snd, artinSchreierTranslation_appTop_root, Scheme.Hom.id_appTop,
          CommRingCat.id_apply, add_sub_cancel_left]
      rw [hd']
      exact FiniteField.lagrangeAt_self _ _
    · let U := W.basicOpen (E m)
      have h0 : U.ι.appTop (d - ψ m.down) = 0 := by
        have := congrArg (fun x ↦ U.ι.appTop x) (FiniteField.lagrangeAt_mul_sub ψ hd m.down)
        simp only [map_mul, map_zero] at this
        exact (Scheme.isUnit_ι_appTop_basicOpen _ (E m)).mul_right_eq_zero.mp this
      rw [map_sub, map_sub, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← RingHom.comp_apply,
        ringHom_zmod_apply] at h0
      rw [hι]
      refine pullback.hom_ext ?_ (by simp)
      refine adjoinRootCover_hom_ext ?_ ?_
      · simp [π, pullback.condition]
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc,
          comp_artinSchreierTranslation_appTop_root]
        linear_combination -h0
  have := fun m ↦ (key m).1
  have hR (m : ULift.{u + 1} (ZMod p)) : (Sigma.ι F m ≫ D).opensRange = W.basicOpen (E m) :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, (key m).2])
  have h := nonempty_isColimit_cofanMk_of (fun m ↦ Sigma.ι F m ≫ D) ?_ ?_
  · rw [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc, cofan_mk_inj] at h
    have hT : Sigma.desc (fun m ↦ Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦
        (adjoinRootCover S P).left) m ≫ D) = D := Sigma.hom_ext _ _ fun m ↦ by simp
    exact hT ▸ h
  · simp_rw [hR]
    refine Scheme.iSup_basicOpen_eq_top_of_sum_eq_one E ?_
    rw [← FiniteField.sum_lagrangeAt ψ d]
    exact Fintype.sum_equiv Equiv.ulift _ _ fun _ ↦ rfl
  · intro a b hab
    simp only [Function.onFun, hR]
    rw [disjoint_iff, ← Scheme.basicOpen_mul,
      FiniteField.lagrangeAt_mul_lagrangeAt ψ hd (fun h ↦ hab (ULift.ext h)),
      Scheme.basicOpen_zero]

end AlgebraicGeometry
