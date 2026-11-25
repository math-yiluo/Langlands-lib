/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Algebra.Homology.VerticalWindowSingleIso
import WeilConjectures.Algebra.Homology.DoubleComplexSingleRowTotalIso

/-!
# Total cohomology of a single smart vertical layer

Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2,
identification of the horizontal cohomology of vertical cohomology.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Total cohomology of the vertical smart layer `[q,q+1)` is iterated cohomology.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2;
Stacks, Homology, lemma-ss-double-complex, item (5).
(blueprint: lem-sp-double-complex-vertical-window-homology).

Proof: after extension by zero, smart truncation at q from below replaces the
q-th column term by its opcycles. Smart truncation at q from above then replaces
that term by the kernel of its outgoing differential. This is canonically the
q-th vertical homology. All other vertical terms are zero. These identifications
are natural in the columns, so the remaining horizontal differential is exactly
the one obtained by applying the q-th homology functor. On the total diagonal
of degree p+q there is only this term, indexed (p,q). The vertical differential
is zero and the horizontal term has sign +1. Thus the three-term complex
computing total homology in degree p+q identifies with the three-term complex
computing horizontal homology in degree p. At p=0 both predecessor terms vanish;
at q=0 extension by zero gives the same kernel and cokernel formulas. The
induced short-complex isomorphism gives the asserted homology isomorphism. -/
theorem verticalWindow_total_homology_iso
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (p q : ℕ) :
    Nonempty ((HomologicalComplex₂.total
      (((verticalWindow (q : ℤ) (q + 1)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) (ComplexShape.up ℕ)).homology (p + q) ≅
      (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology p) := by
  obtain ⟨e⟩ := verticalWindow_single_iso (C := C) q
  let L := ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  have eK := (NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).app K
  obtain ⟨eT⟩ := singleRow_total_iso L q
  exact ⟨HomologicalComplex.homologyMapIso
    (HomologicalComplex₂.total.mapIso eK (ComplexShape.up ℕ)) (p + q) ≪≫
      HomologicalComplex.homologyMapIso eT (p + q) ≪≫
      L.extendHomologyIso (ComplexShape.embeddingUp'Add (1 : ℕ) q) rfl⟩

end HomologicalComplex₂
