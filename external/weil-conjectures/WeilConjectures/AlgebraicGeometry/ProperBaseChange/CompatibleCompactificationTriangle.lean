/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.BaseChange

/-!
# Compatible geometric compactifications of a composable pair

## References

* Stacks Project, More Étale Cohomology, Tag 0F7J, first paragraph and displayed diagram
* Stacks Project, Tag 0F7J, first paragraph
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compatible compactifications over a prescribed compactification of the second morphism. -/
theorem exists_compatible_compactification_triangle
    {X Y Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (d : Compactification g) :
    ∃ e : Compactification (f ≫ d.i), QuasiCompact e.i ∧
      ∃ c : X ⟶ pullback e.g d.i,
        IsOpenImmersion c ∧ QuasiCompact c ∧
        c ≫ pullback.fst e.g d.i = e.i ∧ c ≫ pullback.snd e.g d.i = f ∧
        IsOpenImmersion (pullback.fst e.g d.i) ∧ QuasiCompact (pullback.fst e.g d.i) ∧
        IsProper (pullback.snd e.g d.i) ∧
        IsPullback (pullback.fst e.g d.i) (pullback.snd e.g d.i) e.g d.i ∧
        IsProper (e.g ≫ d.g) ∧ e.i ≫ (e.g ≫ d.g) = f ≫ g := by
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : QuasiSeparatedSpace d.Z := quasiSeparatedSpace_of_quasiSeparated d.g
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let e := NagataCompactification (f ≫ d.i)
  have : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
  have hsq : IsPullback (𝟙 X) f (f ≫ d.i) d.i :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  let c := (e.ofIsPullback hsq).i
  have : QuasiCompact c := (e.ofIsPullback hsq).quasiCompact_openImmersion inferInstance
  refine ⟨e, inferInstance, c, inferInstance, inferInstance, ?_, ?_,
    inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
    inferInstance, ?_⟩
  · exact (e.ofIsPullback_i_fst hsq).trans (Category.id_comp e.i)
  · exact e.ofIsPullback_i_snd hsq
  · rw [← Category.assoc, ← e.comm, Category.assoc, ← d.comm]

end AlgebraicGeometry
