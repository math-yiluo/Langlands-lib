/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperUniversallyClosedImage
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite unions and proper preimages of closed subsets proper over a base

Source: Stacks Project, Cohomology of Schemes, Lemma 30.26.6 (Tag 0CYR)
and Lemma 30.26.5 (Tag 0CYQ), part (3)
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-union-preimage).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Finite unions and proper inverse images preserve properness over a base.

Proof of (1), following the node's seven-step proof:
1. Induct on `n` to reduce to two subsets. The empty scheme proves the `n = 0` case,
   using `lem-weil-pbc-closed-subset-proper-over-base-properties`.
2. Take the reduced induced structures (`lem-weil-pbc-reduced-induced-closed-subscheme`).
   Their coproduct map to `X` is finite by `lem-weil-pbc-closed-immersion-finite` and
   `lem-weil-pbc-finite-coproduct`, hence proper and universally closed by
   `lem-weil-pbc-finite-morphism-permanence` and `lem-weil-pbc-proper-fp-permanence`.
3. The coproduct is proper over `S` by `lem-weil-pbc-proper-coproduct`; its whole closed
   subset is proper by `lem-weil-pbc-closed-subset-proper-over-base-properties`.
4. Apply `lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image`; the image
   equals the union since the coprojections cover the coproduct.
Proof of (2):
5. Form the fibre product with the reduced induced structure on `Z`
   (`def-pc-fibre-product`). Its projections are respectively a closed immersion and proper
   by `lem-weil-pbc-closed-immersion-base-change` and `lem-weil-pbc-proper-fp-permanence`.
6. Its image in `X` is precisely the preimage of `Z`, by
   `lem-weil-pbc-fibre-product-points`: compatible points lift because the tensor product
   of their residue fields is nonzero and has a prime ideal.
7. The composite to `S` is proper by `lem-weil-pbc-proper-fp-permanence`. Apply
   `lem-weil-pbc-closed-subset-proper-over-base-properties` to this closed structure.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.26.6 (Tag 0CYR),
proof; Lemma 30.26.5 (Tag 0CYQ), proof of part (3)
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-union-preimage) -/
theorem isClosedSubsetProperOver_union_preimage
    {X S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] :
    (∀ (n : ℕ) (Z : Fin n → TopologicalSpace.Closeds X),
        (∀ i, IsClosedSubsetProperOver sX (Z i)) →
          IsClosedSubsetProperOver sX (⨆ i, Z i)) ∧
      (∀ {Y : Scheme.{u}} (f : X ⟶ Y) (sY : Y ⟶ S) [LocallyOfFiniteType sY]
          [IsProper f],
        f ≫ sY = sX →
          ∀ (Z : TopologicalSpace.Closeds Y),
            IsClosedSubsetProperOver sY Z →
              IsClosedSubsetProperOver sX (Z.preimage (f := f.base) f.continuous)) := by
  constructor
  · classical
    have hbot : IsClosedSubsetProperOver sX ⊥ := by
      apply (closed_subset_proper_over_base_properties sX ⊥).1.mpr
      refine ⟨⊥_ Scheme, (CategoryTheory.Limits.initial.to X), inferInstance, ?_, inferInstance⟩
      ext x
      simp
    have hunion (A B : TopologicalSpace.Closeds X)
        (hA : IsClosedSubsetProperOver sX A) (hB : IsClosedSubsetProperOver sX B) :
        IsClosedSubsetProperOver sX (A ⊔ B) := by
      let i := (IdealSheafData.vanishingIdeal A).subschemeι
      let j := (IdealSheafData.vanishingIdeal B).subschemeι
      let l : (IdealSheafData.vanishingIdeal A).subscheme ⟶
          (IdealSheafData.vanishingIdeal A).subscheme ⨿
            (IdealSheafData.vanishingIdeal B).subscheme := CategoryTheory.Limits.coprod.inl
      let r : (IdealSheafData.vanishingIdeal B).subscheme ⟶
          (IdealSheafData.vanishingIdeal A).subscheme ⨿
            (IdealSheafData.vanishingIdeal B).subscheme := CategoryTheory.Limits.coprod.inr
      let g := CategoryTheory.Limits.coprod.desc i j
      have : IsProper (i ≫ sX) := hA
      have : IsProper (j ≫ sX) := hB
      have hp : IsProper (g ≫ sX) := by
        change IsProper (CategoryTheory.Limits.coprod.desc i j ≫ sX)
        rw [CategoryTheory.Limits.coprod.desc_comp]
        exact (proper_coproduct_two (i ≫ sX) (j ≫ sX)).2.2.2
      have htop : IsClosedSubsetProperOver (g ≫ sX) ⊤ :=
        (closed_subset_proper_over_base_properties (g ≫ sX) ⊤).1.mpr
          ⟨_, 𝟙 _, inferInstance, by ext x; simp, by simpa using hp⟩
      obtain ⟨W, hW, hpW⟩ :=
        image_isClosedSubsetProperOver_of_universallyClosed (g ≫ sX) sX g rfl ⊤ htop
      have hr : Set.range g = (A : Set X) ∪ (B : Set X) := by
        ext x
        constructor
        · rintro ⟨w, rfl⟩
          have hw : w ∈ Set.range l ∪
              Set.range r := by
            change w ∈ Set.range l ⊔ Set.range r
            dsimp only [l, r]
            rw [(isCompl_range_inl_inr _ _).sup_eq_top]
            trivial
          rcases hw with ⟨a, rfl⟩ | ⟨b, rfl⟩
          · left
            change (CategoryTheory.Limits.coprod.inl ≫ g) a ∈ A
            simp only [g, CategoryTheory.Limits.coprod.inl_desc]
            have hi : Set.range i = (A : Set X) := by simp [i]
            change i a ∈ (A : Set X)
            rw [← hi]
            exact Set.mem_range_self a
          · right
            change (CategoryTheory.Limits.coprod.inr ≫ g) b ∈ B
            simp only [g, CategoryTheory.Limits.coprod.inr_desc]
            have hj : Set.range j = (B : Set X) := by simp [j]
            change j b ∈ (B : Set X)
            rw [← hj]
            exact Set.mem_range_self b
        · intro hx
          have hi : Set.range i = (A : Set X) := by simp [i]
          have hj : Set.range j = (B : Set X) := by simp [j]
          rcases hx with hx | hx
          · rw [← hi] at hx
            obtain ⟨a, rfl⟩ := hx
            exact ⟨l a, by
              change (CategoryTheory.Limits.coprod.inl ≫ g) a = i a
              simp [g]⟩
          · rw [← hj] at hx
            obtain ⟨b, rfl⟩ := hx
            exact ⟨r b, by
              change (CategoryTheory.Limits.coprod.inr ≫ g) b = j b
              simp [g]⟩
      have hEq : W = A ⊔ B := by
        apply TopologicalSpace.Closeds.ext
        simpa [hr] using hW
      rwa [hEq] at hpW
    intro n
    induction n with
    | zero => intro Z hZ; simpa only [iSup_of_empty] using hbot
    | succ n ih =>
      intro Z hZ
      have heq : (⨆ i, Z i) = Z 0 ⊔ ⨆ i : Fin n, Z i.succ := by
        apply le_antisymm
        · apply iSup_le
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · exact le_sup_left
          · exact (le_iSup (fun j : Fin n => Z j.succ) j).trans le_sup_right
        · exact sup_le (le_iSup Z 0) (iSup_le fun j ↦ le_iSup Z j.succ)
      rw [heq]
      exact hunion _ _ (hZ 0) (ih (fun i ↦ Z i.succ) (fun i ↦ hZ i.succ))
  · intro Y f sY _ _ hf Z hZ
    let i := (IdealSheafData.vanishingIdeal Z).subschemeι
    have : IsProper (i ≫ sY) := hZ
    have hp : IsProper (CategoryTheory.Limits.pullback.fst f i ≫ sX) := by
      rw [← hf, ← Category.assoc, CategoryTheory.Limits.pullback.condition, Category.assoc]
      infer_instance
    apply (closed_subset_proper_over_base_properties sX _).1.mpr
    refine ⟨CategoryTheory.Limits.pullback f i,
      CategoryTheory.Limits.pullback.fst f i, inferInstance, ?_, hp⟩
    change Set.range (CategoryTheory.Limits.pullback.fst f i) = f ⁻¹' (Z : Set Y)
    rw [Scheme.Pullback.range_fst]
    simp [i]

end AlgebraicGeometry.Scheme
