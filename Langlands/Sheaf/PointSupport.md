# Supports and compactly supported sections on a site with points

Author: Worker 26. Uses Mathlib's points of sites
(`GrothendieckTopology.Point`: fiber functors, the fiber functor on presheaves
`presheafFiber` and the germ maps `toPresheafFiber`), its criterion for
injectivity on fibers of locally injective maps, its abelian category of module
sheaves and right derived functors. The left-exactness argument follows the
published topological `Langlands.Sheaf.CompactSupport` (Worker 13).

## Data

- A category `C : Type u` with `Category.{v} C` and a Grothendieck topology `J`.
- A family of points `Φ : I → J.Point.{w}` indexed by a type `I : Type uI`;
  each fiber functor takes values in `Type w`.
- A commutative ring `R : Type w`; presheaves take values in `ModuleCat.{w} R`.
  The ring lives in the module universe because Mathlib's exactness of filtered
  colimits for `ModuleCat` is stated in that case.

## Supports

For a module presheaf `F`, an object `X` and `s : F(X)`, `support Φ F s` is the
set of indices `i` such that, for some element `x` of the fiber of `Φ i` over
`X`, the germ `(Φ i).toPresheafFiber X x F s` of `s` at `x` is nonzero
(`mem_support`).

- `support_zero`, `support_add_subset`, `support_smul_subset`: the support of
  `0` is empty, that of a sum lies in the union, that of a multiple in the
  original support. Germ maps are linear.
- `support_map_subset`: restriction along `f : Y ⟶ X` shrinks supports. The
  germ of `F.map f.op s` at `y` is the germ of `s` at the image of `y`
  (Mathlib's `toPresheafFiber_w`).
- `support_app_subset`: a morphism of presheaves shrinks supports (naturality of
  germs). `support_app_of_injective`: if the morphism is injective on the fibers
  of all the points, supports are preserved.
- `mem_support_iff_of_isTerminal` (with `[LocallySmall.{w} C]`): over a terminal
  object each fiber is a singleton, so `i` is in the support exactly when the
  germ of `s` at the unique element of the fiber is nonzero.

## Compactly supported sections

Now `I` carries a topology.

- `IsCompactlySupported Φ F s`: the support lies in some compact subset of `I`.
  Over a compact index space every section qualifies
  (`isCompactlySupported_of_compactSpace`). `IsCompactlySupported.map`: the
  property passes along morphisms of presheaves.
- `compactSubmodule Φ R F X` is the submodule of these sections: the empty set,
  unions of two compact sets and the same compact set witness closure under
  `0`, sums and scalar multiples (`mem_compactSubmodule`).
- `compactSections Φ R X : (Cᵒᵖ ⥤ ModuleCat R) ⥤ ModuleCat R` sends `F` to
  `compactSubmodule Φ R F X` and a morphism to its restriction. It is additive;
  `compactSectionsι` is its injective inclusion
  (`compactSectionsι_app_injective`) into evaluation at `X`.
- `sheafCompactSections J Φ R X` is its composite with `sheafToPresheaf`.

Left exactness, with `[LocallySmall.{w} C]`:

- `injective_presheafFiber_map_kernelι`: the kernel inclusion of a morphism of
  module sheaves is injective on sections, hence locally injective, hence
  injective on the fiber of every point (Mathlib's
  `toPresheafFiber_map_injective`).
- `sheafCompactSections_preservesKernel`: let `s` be a compactly supported
  section of `F` with `f s = 0`. It comes from a section `t` of the kernel, and
  `t` has the same support as `s` by the previous item, so `t` is compactly
  supported. With injectivity of the kernel inclusion this exhibits the image
  of the kernel fork as a kernel in `ModuleCat`.
- With `[HasSheafify J (ModuleCat.{w} R)]`, so that module sheaves form an
  abelian category: `sheafCompactSections_preservesFiniteLimits`.

Compactly supported cohomology, with moreover
`[EnoughInjectives (Sheaf J (ModuleCat.{w} R))]`:
`compactDerived J Φ R X q` is the `q`-th right derived functor of
`sheafCompactSections J Φ R X`. `compactDerivedZeroIso` identifies degree
zero, `compactDerivedIso` computes it from any injective resolution, and
`isZero_compactDerived_succ_of_injective` gives vanishing on injective
sheaves.

## Provenance and scope

Derived infrastructure. Source, read in the original by Worker 26: Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), §1.5, printed pp.10–11 = PDF pp.10–11. Berkovich chooses a
surjective map `I → X`, `i ↦ x_i`, and a geometric point over each `x_i`
(p.10). On p.11: "The support of an element `f ∈ F(X(G))` is the set
`Supp(f) = {x ∈ X | f_x ≠ 0}`, where `f_x` is the image of `f` in `F_x`. It is
a closed subset of `X`. The values of the high direct images of the functor
`F ↦ Γ_{c,X(G)}(F) := {f ∈ F(X(G)) | Supp(f) is compact}` are called the
cohomology groups with compact support".

Correspondence. For the terminal object of the étale site, a family of points
indexed by the points of `X` with its topology (one geometric point over each
point), and an étale sheaf `F`,
`support Φ F f` is Berkovich's `Supp(f)` (by `mem_support_iff_of_isTerminal`)
and `compactDerived` is built in the same way as `H^q_c(X, F)`: the higher
derived functors of compactly supported sections on module sheaves. Differences: the
module works for any site, any family of points and any topological index
space. Compact support means "contained in a compact subset", which agrees with
"compact" when the support is closed and the space is Hausdorff, as in
Berkovich's setting; closedness of supports is not proved here. For a
non-terminal object `X`, `support` is the set of indices with a nonzero germ
at some point of the fiber over `X`, a subset of `I`, not a subset of the
points of `X`. The group action, the equivariant (smooth) version
`Γ_{c,X{G}}` and the analytic specialization are not treated here.

Universes: `C : Type u` with `Category.{v} C`, `I : Type uI`, fibers in
`Type w`, `R : Type w`, modules in `ModuleCat.{w} R`.

Source registration: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
