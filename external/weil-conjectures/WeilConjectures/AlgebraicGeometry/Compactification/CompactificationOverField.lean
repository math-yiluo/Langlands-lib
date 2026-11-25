/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverBase
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# A chosen compactification over a field

Source: blueprint main-20261015, chap-Construction-of-f, sk-def-sfb-dc-setting,
`def-sfb-compactification-over-field.md`, node order 1776
(blueprint: proposition-construction-independence-rf-shriek).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- One compactification of a morphism of `k`-schemes, chosen once and for all.
The source is separated and of finite type over `k`; the target is separated and
quasi-compact over `k`. The chosen object's underlying compactification has maps
`i` and `g` with `i ≫ g = f`, an open immersion `i`, and a proper map `g`;
its full-subcategory membership additionally supplies quasi-compactness of `i`.
No uniqueness or functoriality is asserted.

Source: blueprint main-20261015, chap-Construction-of-f, sk-def-sfb-dc-setting,
`def-sfb-compactification-over-field.md`, node order 1776
(blueprint: proposition-construction-independence-rf-shriek).

Construction: `Spec k` is affine (`def-weil-affine-spectrum`), hence quasi-compact
and quasi-separated (`lem-weil-pbc-affine-scheme-qcqs`). The structure morphisms
and `f.IsOver` give the required triangle (`def-weil-scheme-over-base`). Apply
`compactification_over_base` (`remark-compactifications--1`) with this base
and exactly the displayed relative hypotheses. Apply classical choice to its
nonempty type of compactifications (`definition-compactification-refinement`).
-/
noncomputable def compactificationOverField (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    Compactification.BoundaryCompactification f :=
  Classical.choice (compactification_over_base (S := Spec (.of k)) f)

end AlgebraicGeometry
