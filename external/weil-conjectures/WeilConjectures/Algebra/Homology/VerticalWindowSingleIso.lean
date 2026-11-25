/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.VerticalWindowComponentNaturality

/-!
# The single-degree smart window as a functor

Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2.
(blueprint: lem-sp-vertical-window-single-iso).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The smart window at a single degree is naturally the homology in that degree,
placed in a single-term complex.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2;
Stacks, Homology, lemma-ss-double-complex, item (5).
(blueprint: lem-sp-vertical-window-single-iso).

Proof: extend a nonnegative complex by zero to the integers. Truncation from below
at q gives the cokernel of the incoming differential in degree q. Truncation from
above at q gives the kernel of the induced outgoing differential. The resulting
object is canonically the homology of the original complex in degree q, by the
kernel-in-cokernel description of homology. Every other term vanishes: below q
by the first truncation and above q by the second. Restriction to nonnegative
degrees preserves these identifications. The canonical kernel and cokernel maps
commute with every morphism of complexes, so the component isomorphisms are
natural. At q=0 the incoming differential in the extended complex is zero,
which gives the same homology formula without excluding the boundary case. -/
theorem verticalWindow_single_iso (q : ℕ) :
    Nonempty (verticalWindow (C := C) (q : ℤ) (q + 1) ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q ⋙
        HomologicalComplex.single C (ComplexShape.up ℕ) q) := by
  let F := verticalWindow (C := C) (q : ℤ) (q + 1)
  let G := HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q ⋙
    HomologicalComplex.single C (ComplexShape.up ℕ) q
  let app : ∀ K : CochainComplex C ℕ, F.obj K ≅ G.obj K := fun K ↦
    verticalWindowComponentIso (C := C) q K
  refine ⟨CategoryTheory.NatIso.ofComponents app ?_⟩
  intro K L f
  simpa [app, F, G, HomologicalComplex.homologyFunctor] using
    verticalWindow_component_naturality (C := C) q f

end HomologicalComplex₂
