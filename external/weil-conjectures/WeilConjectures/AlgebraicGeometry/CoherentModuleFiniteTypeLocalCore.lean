/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict

import WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalRestrict
import WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCover

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry
/-- The finite-type clauses of locality for coherent modules.
Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Lemma 01B6.
(blueprint: lem-weil-pbc-coherent-module-finite-type-local-core).

Proof: Coherence of `F` includes finite type. For a point `x` of an open `W`, choose
an open neighbourhood `V` of `x` in `X` on which finitely many sections generate
`F`. Restrict their generating epimorphism to `V ∩ W`. Restriction along an open
immersion preserves the structure module, finite direct sums, and epimorphisms.
Transitivity identifies its target with the restriction of `F|_W` to this open.
These neighbourhoods cover `W`, so `F|_W` is finite type.

Conversely, given coherence of each `F|_(U i)`, project to finite type. For each
point `x` of `X`, the cover equality supplies an `i` with `x ∈ U i`. Choose a finite
family of generators of `F|_(U i)` on a neighbourhood `V` of `x` in `U i`. Since
`U i` is open, the image of `V` is open in `X`; the open-site equivalence and
transitivity identify the generating epimorphism there with one onto `F`.
Thus every point has a neighbourhood with finite generators, proving finite type.
For empty opens the condition is vacuous. An empty covering index forces `X` to
be empty, and both conclusions then follow from the same vacuous condition. -/
theorem coherent_module_finite_type_local_core
    (X : Scheme.{u}) (F : X.Modules) (I : Type u)
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) :
    (RingedSpace.IsCoherent X.toRingedSpace F →
      ∀ (W : X.Opens),
        (Scheme.Modules.restrictFunctor W.ι).obj F |>.IsFiniteType) ∧
      ((∀ (i : I), RingedSpace.IsCoherent (U i).toScheme.toRingedSpace
          ((Scheme.Modules.restrictFunctor (U i).ι).obj F)) → F.IsFiniteType) := by
  constructor
  · intro hF W
    exact coherent_module_finite_type_local_restrict X F hF W
  · intro hF
    exact coherent_module_finite_type_local_cover X F I U hU hF
end AlgebraicGeometry
