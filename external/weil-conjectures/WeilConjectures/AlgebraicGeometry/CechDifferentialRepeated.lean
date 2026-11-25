/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign
import WeilConjectures.AlgebraicGeometry.CechDifferentialRepeatedDecomposition
import WeilConjectures.AlgebraicGeometry.CechDifferentialRepeatedCancellation

/-!
# Cancellation of repeated Čech tuples

Source: Stacks Project, Cohomology of Sheaves, Tag 01FG.
(blueprint: lem-pc-cech-differential-repeated)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The differential of an alternating cochain vanishes on tuples with repetitions.
Source: Stacks 01FG, differential stability of alternating cochains before Definition 01FH.

Proof: choose positions a < b with equal entries. Every face deleting a position other
than a or b still has these equal entries, so its value is zero by hz. If the face deleting
a also has a repetition, then so does the face deleting b, since they differ by a
permutation; both remaining terms vanish. Otherwise the two faces differ by the cycle
moving the surviving equal entry past b-a-1 positions. Its sign is (-1)^(b-a-1).
Apply hc to that cycle. The face signs (-1)^a and (-1)^b make the two surviving
coefficients opposite. Both restriction composites agree in the poset of opens, so
the terms cancel. This works with arbitrary abelian groups, including groups with
2-torsion, without deducing vanishing merely from antisymmetry. For p = 0 the two
faces agree and have coefficients 1 and -1; an empty index type has no such tuple.
(blueprint: lem-pc-cech-differential-repeated) -/
theorem cechDifferential_repeated (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p)
    (hc : ∀ (t : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      c t = (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (c (t ∘ σ)))
    (hz : ∀ t : Fin (p + 1) → I, ¬ Function.Injective t → c t = 0)
    (t : Fin (p + 2) → I) (ht : ¬ Function.Injective t) :
    S.differentialValue F p c t = 0 := by
  obtain ⟨a, b, htab, hab⟩ := Function.not_injective_iff.mp ht
  rw [cechDifferential_repeated_decomposition X U F S p c t a b hab htab hz]
  exact cechDifferential_repeated_cancellation X U F S p c t a b hab htab hc

end AlgebraicGeometry.Scheme
