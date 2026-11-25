/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.Basic.Finite.Sigma
import WeilConjectures.AlgebraicGeometry.SiteCoveringIsomorphicFamily

/-! # Finite coverings on the pair categories

Source: Stacks Project, Categories 004A and Sites 00VH, 0A34.
(blueprint: lem-weil-pbc-site-system-finite-coverings)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite presieves whose image under evaluation covers.
Source: Stacks 00VH, the finite-family site transported across the evaluation equivalence.
(blueprint: lem-weil-pbc-site-system-finite-coverings) -/
def finiteEquivalencePrecoverage {A B : Type u} [Category.{v} A] [Category.{v} B]
    (p : A ⥤ B) (P : Precoverage B) : Precoverage A := Precoverage.finite A ⊓ P.comap p

variable {A B : Type u} [Category.{v} A] [Category.{v} B]
  (p : A ⥤ B) (P : Precoverage B)

instance [P.HasIsos] : (finiteEquivalencePrecoverage p P).HasIsos where
  mem_coverings_of_isIso f :=
    ⟨Precoverage.mem_coverings_of_isIso (J := Precoverage.finite A) f,
      Precoverage.mem_coverings_of_isIso (J := P.comap p) f⟩

instance [P.IsStableUnderFiniteComposition] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteComposition where
  comp_mem_coverings {ι} [Finite ι] {_S} {_X} f hf {σ} [∀ i, Finite (σ i)] {_Y} g hg := by
    refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
    change (Presieve.ofArrows _ _).map p ∈ P _
    rw [Presieve.map_ofArrows]
    simpa only [Functor.map_comp] using
      Precoverage.IsStableUnderFiniteComposition.comp_mem_coverings
        (J := P) (fun i ↦ p.map (f i))
        (by simpa only [Presieve.map_ofArrows] using
          (show (Presieve.ofArrows _ f).map p ∈ P _ from hf.2))
        (fun i j ↦ p.map (g i j))
        (fun i ↦ by simpa only [Presieve.map_ofArrows] using
          (show (Presieve.ofArrows _ (g i)).map p ∈ P _ from (hg i).2))

instance [p.IsEquivalence] [P.IsStableUnderFiniteBaseChange] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteBaseChange where
  mem_coverings_of_isPullback {ι} [Finite ι] {_S} {_X} f hf {_Y} g {_Z} p₁ p₂ h := by
    refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
    change (Presieve.ofArrows _ _).map p ∈ P _
    rw [Presieve.map_ofArrows]
    exact Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
      (J := P) (fun i ↦ p.map (f i))
      (by simpa only [Presieve.map_ofArrows] using
          (show (Presieve.ofArrows _ f).map p ∈ P _ from hf.2)) (p.map g)
      (fun i ↦ p.map (p₁ i)) (fun i ↦ p.map (p₂ i)) (fun i ↦ (h i).map p)

instance [p.IsEquivalence] [P.HasPullbacks] :
    (finiteEquivalencePrecoverage p P).HasPullbacks where
  hasPullbacks_of_mem f hR := (P.comap p).hasPullbacks_of_mem f hR.2

end CategoryTheory
