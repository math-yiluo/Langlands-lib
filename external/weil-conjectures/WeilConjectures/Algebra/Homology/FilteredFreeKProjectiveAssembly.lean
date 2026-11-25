/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Abelian

import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import WeilConjectures.Algebra.Homology.CoproductKProjective
import WeilConjectures.Algebra.Homology.FilteredFreeTelescopeSplitting

/-! Telescope assembly sublemma for filtered K-projective complexes. -/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private theorem isKProjective_of_degreewise_split
    {A : Type u} [CommRing A]
    (S : ShortComplex (CochainComplex (ModuleCat.{max u v} A) ℤ))
    (σ : ∀ k, (S.map (HomologicalComplex.eval (ModuleCat.{max u v} A) (.up ℤ) k)).Splitting)
    (h₁ : S.X₁.IsKProjective) (h₂ : S.X₂.IsKProjective) : S.X₃.IsKProjective := by
  rw [isKProjective_iff_leftOrthogonal] at h₁ h₂ ⊢
  apply (HomotopyCategory.subcategoryAcyclic (ModuleCat.{max u v} A)).leftOrthogonal
    |>.ext_of_isTriangulatedClosed₃ (trianglehOfDegreewiseSplit S σ) ?_ h₁ h₂
  exact (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
    ⟨S, σ, ⟨Iso.refl _⟩⟩

/-- The union of a degreewise split filtration by K-projective stages is K-projective.
Source: Stacks Project, Tags 09KL--09KM.
(blueprint: lem-pc-filtered-free-kprojective-assembly)

Proof: form the actual direct sum S of the stages and the maps a = identity minus
successor and b = augmentation. Compatibility proves a followed by b is zero.
The construction lemma supplies a splitting of this sequence in every degree,
independently of K-projectivity. For a map S -> N with N acyclic, restrict to each
summand and use its K-projectivity to choose a null homotopy. Evaluation preserves
coproducts, so the homotopy components assemble; their support and homotopy identities
hold on every summand. Thus S is K-projective. The degreewise split short complex
gives a distinguished triangle S -> S -> P -> S[1] in the homotopy category.
K-projectivity is left orthogonality to acyclic objects. This orthogonal is a
triangulated subcategory, so its closure under third objects proves P K-projective
from the two copies of S. The zero-stage hypothesis is unnecessary for this argument but is
retained in the signature. -/
theorem filtered_free_telescope_assembly
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hstage : ∀ n, (F n).IsKProjective) :
    P.IsKProjective := by
  classical
  cases hzero
  let S := ShortComplex.mk (filteredTelescopeMap F step)
    (filteredTelescopeAugmentation P F ι) (filteredTelescope_comp_zero P F ι step hcompat)
  have hS : (∐ F).IsKProjective := isKProjective_coproduct F hstage
  have σ := filteredTelescope_degreewise_splitting P F ι step hmono hcompat
    hexhaustive hsplit
  exact isKProjective_of_degreewise_split S (fun k ↦ (σ k).some) hS hS

end CochainComplex
