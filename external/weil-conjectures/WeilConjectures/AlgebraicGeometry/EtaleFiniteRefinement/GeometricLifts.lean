/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Lifts of geometric points along an étale morphism

For a morphism `f : X ⟶ S`, a field `K` and a `K`-point `σ : Spec K ⟶ S`, a *lift* of `σ` is a
morphism `x : Spec K ⟶ X` with `x ≫ f = σ`. We say that `f` has *at most `d` geometric lifts*
if no separably closed point of `S` has `d + 1` distinct lifts; for an étale `f` this bounds the
number of points of the geometric fibres of `f` by `d`.

For an étale `f`, the number of lifts of a separably closed point only depends on its image in
`S`: lifts along a field extension `L ⟶ Ω` with `L` separably closed are bijective, and any two
points of `S` with the same image have a common field extension.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.HasAtMostGeometricLifts`: `f` has at most `d` geometric lifts.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_injective_lifts_of_apply_eq`: for étale `f`, `n`
  distinct lifts of a field-valued point give `n` distinct lifts of every separably closed
  point with the same image.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A morphism `f : X ⟶ S` *has at most `d` geometric lifts* if for every separably closed
field `K` and every `σ : Spec K ⟶ S` there are no `d + 1` distinct morphisms
`x : Spec K ⟶ X` with `x ≫ f = σ`. For an étale `f`, this says that the geometric fibres of `f`
have at most `d` points. -/
def Scheme.Hom.HasAtMostGeometricLifts (f : X ⟶ S) (d : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [IsSepClosed K] (σ : Spec (.of K) ⟶ S)
    (x : Fin (d + 1) → (Spec (.of K) ⟶ X)), (∀ i, x i ≫ f = σ) → ¬ Function.Injective x

/-- For an étale `f`, every lift of `Spec Ω ⟶ Spec L ⟶ S` along `f` with `L` separably closed
comes from a lift of `Spec L ⟶ S`. -/
lemma Scheme.Hom.exists_SpecMap_comp_eq_of_isSepClosed (f : X ⟶ S) [Etale f] {L Ω : Type u}
    [Field L] [IsSepClosed L] [Field Ω] (β : CommRingCat.of L ⟶ CommRingCat.of Ω)
    (τ : Spec (.of L) ⟶ S) (g : Spec (.of Ω) ⟶ X) (hg : g ≫ f = Spec.map β ≫ τ) :
    ∃ g' : Spec (.of L) ⟶ X, Spec.map β ≫ g' = g ∧ g' ≫ f = τ := by
  obtain ⟨c, hc⟩ := exists_eq_spec_map_comp_fromSpecResidueField g _ rfl
  obtain ⟨b, hb⟩ := exists_eq_spec_map_comp_fromSpecResidueField τ _ rfl
  have hs : f (g (closedPoint Ω)) = τ (closedPoint L) := by
    have := congr($hg (closedPoint Ω))
    simpa only [Scheme.Hom.comp_apply, SpecMap_apply_closedPoint] using this
  rw [← S.residueFieldCongr_fromSpecResidueField hs, ← Category.assoc, ← Spec.map_comp] at hb
  have key : f.residueFieldMap (g (closedPoint Ω)) ≫ c =
      ((S.residueFieldCongr hs).hom ≫ b) ≫ β := by
    rw [hc, hb, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp] at hg
    exact Spec.map_injective ((cancel_mono _).1 hg)
  let : Algebra (S.residueField (f (g (closedPoint Ω)))) (X.residueField (g (closedPoint Ω))) :=
    (f.residueFieldMap _).hom.toAlgebra
  obtain ⟨c', hc'⟩ := RingHom.exists_comp_eq_of_isSepClosed
    (E := X.residueField (g (closedPoint Ω))) ((S.residueFieldCongr hs).hom ≫ b).hom β.hom
    c.hom (congr_arg CommRingCat.Hom.hom key)
  refine ⟨Spec.map (CommRingCat.ofHom c') ≫ X.fromSpecResidueField _, ?_, ?_⟩
  · refine Eq.trans ?_ hc.symm
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact congr($hc' a)
  · have h' : f.residueFieldMap _ ≫ CommRingCat.ofHom c' = (S.residueFieldCongr hs).hom ≫ b := by
      ext a
      apply β.hom.injective
      exact congr($hc' (f.residueFieldMap _ a)).trans congr(($key).hom a)
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, h']
    exact hb.symm

/-- **The number of geometric lifts along an étale morphism only depends on the image point.**
Let `f : X ⟶ S` be étale and let `σ : Spec K ⟶ S`, `τ : Spec L ⟶ S` have the same image, with
`L` separably closed. Then `n` distinct lifts of `σ` along `f` give `n` distinct lifts of `τ`. -/
theorem Scheme.Hom.exists_injective_lifts_of_apply_eq (f : X ⟶ S) [Etale f] {K L : Type u}
    [Field K] [Field L] [IsSepClosed L] (σ : Spec (.of K) ⟶ S) (τ : Spec (.of L) ⟶ S)
    (h : σ (closedPoint K) = τ (closedPoint L)) {n : ℕ} (x : Fin n → (Spec (.of K) ⟶ X))
    (hx : ∀ i, x i ≫ f = σ) (hinj : Function.Injective x) :
    ∃ y : Fin n → (Spec (.of L) ⟶ X), (∀ i, y i ≫ f = τ) ∧ Function.Injective y := by
  obtain ⟨Ω, _, α, β, hαβ⟩ := exists_SpecMap_comp_eq_of_apply_eq σ τ h
  have H (i : Fin n) : ∃ g' : Spec (.of L) ⟶ X, Spec.map β ≫ g' = Spec.map α ≫ x i ∧ g' ≫ f = τ :=
    f.exists_SpecMap_comp_eq_of_isSepClosed β τ (Spec.map α ≫ x i)
      (by rw [Category.assoc, hx i, hαβ])
  choose y hy₁ hy₂ using H
  refine ⟨y, hy₂, fun i j hij ↦ hinj ?_⟩
  exact Scheme.SpecMap_comp_injective α ((hy₁ i).symm.trans (hij ▸ hy₁ j))

end AlgebraicGeometry
