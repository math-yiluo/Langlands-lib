module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Morphisms of finite presentation

A morphism of schemes is of finite presentation at a point if, on suitable affine
neighbourhoods of that point and its image, the induced ring map is of finite
presentation. It is locally of finite presentation when this holds at every point, and it
is of finite presentation when it is additionally quasi-compact and quasi-separated.

Part (1) of Stacks 01TP is `AlgebraicGeometry.FinitePresentationAt`; affine neighbourhoods
are bundled as `Scheme.affineOpens`, and their coordinate ring map is `Scheme.Hom.appLE`.
Part (2) is Mathlib's `AlgebraicGeometry.LocallyOfFinitePresentation`, whose
`HasRingHomProperty.iff_exists_appLE` characterization identifies it with the pointwise
condition defined here. Part (3) is the conjunction of Mathlib's three constituent
morphism properties; its projection lemmas make the corresponding typeclass assumptions
available to clients.

## Main definitions

* `AlgebraicGeometry.FinitePresentationAt` expresses finite presentation at a point.
* `AlgebraicGeometry.LocallyOfFinitePresentation` (Mathlib) expresses local finite
  presentation.
* `AlgebraicGeometry.FinitePresentation` expresses finite presentation.

## Main results

* `AlgebraicGeometry.finitePresentation_isStableUnderBaseChange`: finite presentation is stable
  under base change.

## References

* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 01TS](https://stacks.math.columbia.edu/tag/01TS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is of finite presentation if it is locally of finite
presentation, quasi-compact, and quasi-separated. -/
@[stacks 01TP "part (3)"]
public abbrev FinitePresentation {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

/-- A morphism of finite presentation is locally of finite presentation. -/
public lemma FinitePresentation.locallyOfFinitePresentation {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FinitePresentation f) : LocallyOfFinitePresentation f := hf.1

end AlgebraicGeometry
