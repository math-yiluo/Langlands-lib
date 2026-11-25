/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafLocalExact
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafDifferentialInnerInverse
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Local alternating Čech cancellation

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem exact_inner_inverse_on_cycles
    {A : Type*} [Category A] [Abelian A] (S : ShortComplex A) (hS : S.Exact)
    (s : S.X₂ ⟶ S.X₁) (hs : S.f ≫ s ≫ S.f = S.f)
    {T : A} (a : T ⟶ S.X₂) (ha : a ≫ S.g = 0) : a ≫ s ≫ S.f = a := by
  have : Epi (Limits.kernel.lift S.g S.f S.zero) := hS.epi_kernelLift
  have hi : Limits.kernel.ι S.g ≫ s ≫ S.f = Limits.kernel.ι S.g := by
    apply (cancel_epi (Limits.kernel.lift S.g S.f S.zero)).mp
    simpa only [← Category.assoc, Limits.kernel.lift_ι] using hs
  rw [← Limits.kernel.lift_ι S.g a ha]
  simp only [Category.assoc, hi]

/-- Positive-degree signed insertion cancellation on the singleton open.
Source: Stacks Project, Tag 02FU, with the ordered convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-positive-contraction).

Proof: On a test open V contained in U i, for a tuple t not containing i,
insert i in its unique increasing position b. Project to that coordinate and
multiply by (-1)^b. The resulting intersection equals the old intersection
since V is contained in U i. For tuples containing i use zero. These linear maps
commute with restrictions. For a positive-degree tuple not containing i, deleting
the inserted i contributes the identity. Every other deletion in d h is paired
with insertion after deletion in h d; the two restrictions agree and their signs
are opposite. For tuples containing i, only deletion of i contributes, with
product of signs one. Sheafify these natural maps on the restricted site,
using the local sheafification identification with the restriction of the
sheafified complex; additivity preserves the equation. Transport through
extendXIso to integer degrees and put the maps equal to zero in negative degrees.
For empty test opens all modules vanish; r=0 has no i; degrees above the tuple
length have zero terms. This claim imposes no equation at degree zero.
-/
theorem alternatingCechSheaf_restrict_positive_contraction
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
      ∀ k : ℤ, 0 < k → C.d k (k + 1) ≫ h k +
        (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
          h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by
  classical
  dsimp only
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
  have hs : ∀ k : ℤ, ∃ s : C.X (k + 1) ⟶ C.X k,
      C.d k (k + 1) ≫ s ≫ C.d k (k + 1) = C.d k (k + 1) :=
    fun k ↦ alternatingCechSheaf_restrict_differential_inner_inverse U G i k
  -- The choices are internal to this existential proof; no definition depends on them.
  choose s hs using hs
  -- An inner inverse of the incoming differential projects onto its image.
  let q : ∀ k : ℤ, C.X k ⟶ C.X k := fun k ↦
    (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
      s (k - 1) ≫ C.d (k - 1) k
  have qd (k j : ℤ) : q k ≫ C.d k j = 0 := by
    simp only [q, Category.assoc, C.d_comp_d, Limits.comp_zero]
  -- Normalizing the unrelated inner inverses supplies compatible homotopy equations.
  let h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k := fun k ↦ s k ≫ (𝟙 _ - q k)
  refine ⟨h, ?_⟩
  intro k hk
  have he : (C.sc' (k - 1) k (k + 1)).Exact :=
    alternatingCechSheaf_restrict_local_exact U G i k hk
  let t : C.X k ⟶ C.X (k - 1) :=
    (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫ s (k - 1)
  have ht : C.d (k - 1) k ≫ t ≫ C.d (k - 1) k = C.d (k - 1) k := by
    have e := congrArg (fun f ↦ f ≫
      (C.XIsoOfEq (show k = k - 1 + 1 by omega)).inv) (hs (k - 1))
    simp only [Category.assoc, C.d_comp_XIsoOfEq_inv] at e
    dsimp only [t]
    simp only [← Category.assoc, C.d_comp_XIsoOfEq_hom]
    simpa only [Category.assoc] using e
  let a : C.X k ⟶ C.X k := 𝟙 _ - C.d k (k + 1) ≫ s k
  have ha : a ≫ C.d k (k + 1) = 0 := by
    simp only [a, Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, sub_self]
  have haq : a ≫ q k = a :=
    exact_inner_inverse_on_cycles (C.sc' (k - 1) k (k + 1)) he t ht a ha
  have hprev : h (k - 1) ≫ C.d (k - 1) k = s (k - 1) ≫ C.d (k - 1) k := by
    simp only [h, Category.assoc, Preadditive.sub_comp, Category.id_comp, qd,
      sub_zero]
  change C.d k (k + 1) ≫ h k +
    (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
      h (k - 1) ≫ C.d (k - 1) k = 𝟙 _
  rw [hprev]
  change C.d k (k + 1) ≫ (s k ≫ (𝟙 _ - q k)) + q k = 𝟙 _
  simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc]
  dsimp only [a] at haq
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc] at haq
  rw [Category.assoc]
  calc
    C.d k (k + 1) ≫ s k - C.d k (k + 1) ≫ s k ≫ q k + q k =
        C.d k (k + 1) ≫ s k + (q k - C.d k (k + 1) ≫ s k ≫ q k) := by abel
    _ = C.d k (k + 1) ≫ s k + (𝟙 _ - C.d k (k + 1) ≫ s k) := by rw [haq]
    _ = 𝟙 _ := by abel

end AlgebraicGeometry
