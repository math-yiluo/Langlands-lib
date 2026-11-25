/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.Dense

/-!

# Dense compactifications of finite presentation over a locally Noetherian base

The compactification datum the construction `Rf_! = Rp_* j_!` of the proper base change
chapter asks for consists of a factorisation `f = j ≫ p` in which `j` is a
scheme-theoretically dense open immersion *and* `p` is proper *and locally of finite
presentation* (blueprint: `proper_base_change.tex`, §A43, `BA43-DENSE-DATA`). Over a general
quasi-compact quasi-separated base the two halves are available separately —
`AlgebraicGeometry.exists_isDense_compactification` for density and
`AlgebraicGeometry.exists_compactification_locallyOfFinitePresentation` for finite
presentation — but not at once.

Over a *locally Noetherian* base there is nothing to reconcile: the structure morphism of any
compactification whatsoever is proper, hence locally of finite type, hence locally of finite
presentation (`AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g`). This file
records the two resulting statements, obtained by adding that observation to the dense
compactification of `AlgebraicGeometry.Compactification.Dense` and to the dense common
refinement of `AlgebraicGeometry.Compactification.CommonRefinement`.

## Main results

- `AlgebraicGeometry.exists_isDense_compactification_locallyOfFinitePresentation`
  (blueprint: `proper_base_change.tex`, §A43, `BA43-DENSE-DATA`): over a locally Noetherian
  quasi-compact quasi-separated base, a separated, quasi-compact morphism locally of finite
  type admits a dense compactification whose structure morphism is locally of finite
  presentation;
- `AlgebraicGeometry.Compactification.exists_common_refinement_isDense_locallyOfFinitePresentation`
  (blueprint: `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`): over a locally Noetherian base, two
  compactifications of a quasi-compact morphism are refined by a common one that is
  scheme-theoretically dense and whose structure morphism is locally of finite presentation.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

variable (f) in
/-- **A dense compactification of finite presentation over a locally Noetherian base**
(blueprint: `proper_base_change.tex`, §A43, `BA43-DENSE-DATA`).

Over a locally Noetherian quasi-compact quasi-separated base, the chosen dense
compactification `AlgebraicGeometry.denseCompactification` already has structure morphism
locally of finite presentation, so `BA43-DENSE-DATA` is delivered in full. -/
theorem exists_isDense_compactification_locallyOfFinitePresentation [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsLocallyNoetherian Y] :
    ∃ c : Compactification f, c.IsDense ∧ LocallyOfFinitePresentation c.g :=
  ⟨denseCompactification f, denseCompactification_isDense f,
    (denseCompactification f).locallyOfFinitePresentation_g⟩

/-- **A dense common refinement of finite presentation over a locally Noetherian base**
(blueprint: `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`).

The common refinement produced by
`AlgebraicGeometry.Compactification.exists_common_refinement_isSchemeTheoreticallyDominant`
has structure morphism locally of finite presentation as soon as the base is locally
Noetherian. No quasi-compactness or quasi-separatedness of `Y` is needed, since the two
compactifications being refined are given. -/
theorem Compactification.exists_common_refinement_isDense_locallyOfFinitePresentation
    [QuasiCompact f] [IsLocallyNoetherian Y] (c d : Compactification f) :
    ∃ e : Compactification f, e.IsDense ∧ LocallyOfFinitePresentation e.g ∧
      Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d) :=
  let ⟨e, he, hc, hd⟩ := exists_common_refinement_isSchemeTheoreticallyDominant c d
  ⟨e, he, e.locallyOfFinitePresentation_g, hc, hd⟩

end AlgebraicGeometry
