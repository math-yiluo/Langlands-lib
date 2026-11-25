/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation

import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitUnionPresentation

/-! # Gluing flat counit presentations

Source: Stacks Project, Tags 0DJ9 and 08DR.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Bounded flat presentations glue across a two-open cover.
Source: Stacks Project, Tag 0DJ9, relative Mayer--Vietoris induction step;
Tag 08DR, quasi-compact-open induction.
(blueprint: lem-pc-standard-single-flat-counit-union).

Proof: Put W = U union V. Restrict a relatively flat quasi-coherent module N on W
to U, V and U intersect V. Relative flatness and quasi-coherence survive these
open restrictions. Apply the three hypotheses to obtain bounded flat complexes
on B and direct-image identifications. Mayer--Vietoris identifies R(W -> B)_*N
with the shifted cone of the restriction-difference arrow from the sum of the
two complexes to the overlap complex. Replace these three complexes by bounded
above projective resolutions over the affine base section ring and sheafify.
Use the affine equivalence between the bounded-above derived category of section
modules and derived sheaves with quasi-coherent cohomology. In the section-module
category, bounded-above projective complexes lift the restriction-difference arrow
to a chain map; sheafify this map and form its shifted cone K. This does not claim
that a free quasi-coherent sheaf is projective among all sheaves. The replacements
are joined to the original flat presentations by quasi-isomorphisms between K-flat
complexes, so ordinary g-pullback preserves them and the counit squares commute.
Finite sums, shifts and cones preserve flat terms and an upper bound. The original
Mayer--Vietoris triangle gives the base iso e.
On A, ordinary pullback takes this cone to the cone of the pulled-back arrow.
The canonical comparisons commute with restriction and the Mayer--Vietoris
boundary (from their unit-and-counit definition). On the three previous flat
complexes the universal counits are invertible because bounded flat complexes
are K-flat. Therefore their given factorizations identify the target restriction
arrows, not just the target objects, with ordinary pullback of the lifted arrow.
The base-changed Mayer--Vietoris triangle consequently supplies t for the union.
Naturality of the universal counit on the cone, and the morphism of these two
triangles, give the required factorization on W. Quasi-separatedness makes the
overlap quasi-compact; being open in affine V it is separated, so the finite
alternating Cech calculation supplies its models in the induction. Empty or
repeated opens give zero or redundant cones and the same argument applies.
Every witness is destructured in a proof, not chosen to define a sheaf or complex. -/
theorem standardSingleFlatCounitOnOpen_union
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (hU : IsCompact (U : Set Y)) (hV : IsAffineOpen V)
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    StandardSingleFlatCounitOnOpen p g (U ⊔ V) := by
  intro N _ hN
  let _ := hU
  let _ := hV
  exact standardSingleFlatCounitPresentation_union_of_open_presentations
    p g U V N hN hPU hPV hPUV

end AlgebraicGeometry
