/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactExtensions

/-! # Factoring alpha-compact objects through a bounded localizing hull

Source: Krause (2001), Lemma 5, page 125.
(blueprint: lem-sfb-alpha-compact-factor-through)
-/

@[expose] public section

universe v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{v} C]

private def ReceivesThrough (S H : ObjectProperty C) (Y : C) : Prop :=
  ∀ X, S X → ∀ f : X ⟶ Y,
    ∃ Z, H Z ∧ ∃ (a : X ⟶ Z) (b : Z ⟶ Y), a ≫ b = f

/-- Alpha-compact objects are retracts of objects of any triangulated bounded-sum
hull contained in the canonical class and containing localizing generators.
Source: Krause (2001), Lemma 5, page 125, the factor-through subcategory.
(blueprint: lem-sfb-alpha-compact-factor-through)

Proof: let R be the objects receiving only maps from alpha-compact objects which
factor through H. It contains H and is invariant under isomorphism and shifts.
For a coproduct, (G4) factors component maps through alpha-compact objects;
membership in R factors these through H, and alpha-smallness restricts the
result to fewer than alpha summands. For a cone, factor the connecting map
through H0 and take its fiber X'. Extension closure puts X' in the canonical
class. Factor its lift to the preceding vertex through H1. Complete the square
to a cone H2 of H0[-1] to H1. The discrepancy factors through H0, so the original
map factors through H2 plus H0. Hence R is localizing. Generation makes R all
of C, and the factorization of each identity exhibits the claimed retract. -/
theorem alphaCompactObjects_le_retractClosure
    (α : Cardinal.{v}) [Fact α.IsRegular]
    (G H : ObjectProperty C) [H.IsClosedUnderIsomorphisms] [H.IsTriangulated]
    (hHS : H ≤ alphaCompactObjects C α)
    (hsum : ∀ (I : Type v) (Y : I → C), HasCardinalLT I α →
      (∀ i, H (Y i)) → H (∐ Y))
    (hGH : G ≤ H)
    (hGgen : ∀ (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsTriangulated],
      (∀ (I : Type v) (Y : I → C), (∀ i, S (Y i)) → S (∐ Y)) →
      G ≤ S → ∀ X, S X) :
    alphaCompactObjects C α ≤ H.retractClosure := by
  classical
  let S := alphaCompactObjects C α
  have : S.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun X hX ↦ hX.shift n⟩⟩
  have : S.ContainsZero := ⟨0, isZero_zero C, isAlphaCompact_zero α⟩
  have : S.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    IsAlphaCompact.extension α T hT h₁ h₃)
  have : S.IsTriangulated := {}
  let R : ObjectProperty C := ReceivesThrough S H
  have hHR : H ≤ R := by
    intro Y hY X hX f
    exact ⟨Y, hY, f, 𝟙 Y, Category.comp_id _⟩
  have : R.IsClosedUnderIsomorphisms := ⟨by
    intro Y Y' e hY X hX f
    obtain ⟨Z, hZ, a, b, hab⟩ := hY X hX (f ≫ e.inv)
    refine ⟨Z, hZ, a, b ≫ e.hom, ?_⟩
    rw [← Category.assoc, hab, Category.assoc, e.inv_hom_id, Category.comp_id]⟩
  have : R.ContainsZero := ⟨0, isZero_zero C, hHR _ H.prop_zero⟩
  have : R.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro Y hY X hX f
    let e := shiftEquiv C n
    let adj := e.symm.toAdjunction
    obtain ⟨Z, hZ, a, b, hab⟩ := hY (e.inverse.obj X) (hX.shift (-n))
      ((adj.homEquiv X Y).symm f)
    refine ⟨e.functor.obj Z, H.le_shift n _ hZ,
      adj.homEquiv X Z a, e.functor.map b, ?_⟩
    change (adj.homEquiv X Z) a ≫ e.symm.inverse.map b = f
    rw [← adj.homEquiv_naturality_right, hab, Equiv.apply_symm_apply]⟩⟩
  have : R.IsTriangulatedClosed₃ := .mk' (by
    intro T hT hY₀ hY₁ X hX f
    have hY₀' := R.le_shift (1 : ℤ) _ hY₀
    obtain ⟨H₀, hH₀, a, b, hab⟩ := hY₀' X hX (f ≫ T.mor₃)
    obtain ⟨X', l, δ, hTT⟩ := distinguished_cocone_triangle₁ a
    let TT := Triangle.mk l a δ
    have hX' : S X' := S.ext_of_isTriangulatedClosed₁ TT hTT hX (hHS _ hH₀)
    obtain ⟨c, hc₁, hc₃⟩ := complete_distinguished_triangle_morphism₁ TT T.rotate
      hTT (rot_of_distTriang _ hT) f b hab
    let φ : TT ⟶ T.rotate :=
      { hom₁ := c, hom₂ := f, hom₃ := b,
        comm₁ := hc₁, comm₂ := hab, comm₃ := hc₃ }
    let φ' := (invRotate C).map φ
    obtain ⟨H₁, hH₁, q, r, hqr⟩ := hY₁ X' hX' c
    let d := TT.invRotate.mor₁ ≫ q
    obtain ⟨H₂, hH₂, m, n, hD⟩ := H.distinguished_cocone_triangle d
      (H.le_shift (-1) _ hH₀) hH₁
    let D := Triangle.mk d m n
    have hcomm : d ≫ r = φ'.hom₁ ≫ T.rotate.invRotate.mor₁ := by
      rw [show d = TT.invRotate.mor₁ ≫ q from rfl, Category.assoc, hqr]
      exact φ'.comm₁
    obtain ⟨t, ht, _⟩ := complete_distinguished_triangle_morphism D
      T.rotate.invRotate hD (inv_rot_of_distTriang _ (rot_of_distTriang _ hT))
      φ'.hom₁ r hcomm
    obtain ⟨s, hs, _⟩ := complete_distinguished_triangle_morphism TT.invRotate D
      (inv_rot_of_distTriang _ hTT) hD (𝟙 _) q (by simp [D, d])
    change X ⟶ H₂ at s
    change H₂ ⟶ T.obj₃ at t
    have hdiff : l ≫ (f - s ≫ t) = 0 := by
      have hs' : l ≫ s = q ≫ m := hs
      have ht' : m ≫ t = r ≫ T.mor₂ := ht
      have hc' : l ≫ f = c ≫ T.mor₂ := hc₁
      rw [Preadditive.comp_sub, ← Category.assoc, hs', Category.assoc, ht',
        ← Category.assoc, hqr, ← hc', sub_self]
    obtain ⟨z, hz⟩ := TT.yoneda_exact₂ hTT _ hdiff
    refine ⟨H₂ ⊞ H₀, H.ext_of_isTriangulatedClosed₂ _
      (binaryBiproductTriangle_distinguished H₂ H₀) hH₂ hH₀,
      biprod.lift s a, biprod.desc t z, ?_⟩
    rw [biprod.lift_desc]
    change f - s ≫ t = a ≫ z at hz
    rw [← hz]
    abel)
  have : R.IsTriangulatedClosed₂ := .of_isTriangulatedClosed₃
  have : R.IsTriangulated := {}
  have hRsum (I : Type v) (Y : I → C) (hY : ∀ i, R (Y i)) : R (∐ Y) := by
    intro X hX f
    obtain ⟨Z, hZ, a, g, hg⟩ := IsAlphaCompact.factorizationClass α X hX I Y f
    choose W hW b c hbc using fun i ↦ hY i (Z i) (hZ i) (a i)
    obtain ⟨J, hJ, q, hq⟩ := hX.isAlphaSmall I W (g ≫ Limits.Sigma.map b)
    let w : (∐ fun j : J ↦ W j) ⟶ ∐ Y :=
      Sigma.desc (fun j : J ↦ c j ≫ Sigma.ι Y j)
    refine ⟨∐ fun j : J ↦ W j, hsum J _ hJ (fun j ↦ hW j), q, w, ?_⟩
    have hw : w = Sigma.desc (fun j : J ↦ Sigma.ι W j) ≫ Limits.Sigma.map c := by
      apply Sigma.hom_ext
      intro j
      simp [w]
    rw [hw, ← Category.assoc, hq, Category.assoc, Limits.Sigma.map_comp_map]
    simpa only [hbc] using hg
  have hR := hGgen R hRsum (hGH.trans hHR)
  intro X hX
  obtain ⟨Z, hZ, a, b, hab⟩ := hR X X hX (𝟙 X)
  exact ⟨Z, hZ, ⟨{ i := a, r := b, retract := hab }⟩⟩

end CategoryTheory
