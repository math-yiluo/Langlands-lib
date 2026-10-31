# The coordinate uniformity on actual right-compatible families

Authors: Worker 6 and Worker 1126.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.1.1–I.1.2, printed pp.6–7/PDF12–13, supply the corner order and
finite local units. I.1.3, printed p.8/PDF14, gives the topology of `A`
by the basis `A(1-e)` of zero neighborhoods and builds the inverse
limit `Ā = lim Ae`. Printed p.9/PDF15 gives the topology on `Ā`: it is
invariant under left translation, with the zero-neighborhood basis
`Ā(1-e) := {ā ∈ Ā | ā(e) = 0}`, `e ∈ Idem(A)`. The same page states that
`A` embeds canonically and continuously in `Ā` by `a ↦ ā`, `ā(e) = a e`.

PDF14–15 were read for this module. No source-specific errata note is
present in the project. The registered 2010-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
correct on their first page the pseudometric order (2010 p.9, now
`d_e ≤ d_f` for `e ≤ f`) and a local-unit formula (2010 p.11). The 2026
text already prints the corrected order, and neither entry concerns
the family topology used here.

## Construction

Everything is stated for the original `A : Type uA` with
`NonUnitalRing A` and the published additive group
`IdempotentedRingRightLimit A` of actual compatible families. Its
addition and subtraction are the original pointwise operations.

- `coordinate e` is the actual evaluation `x ↦ x(e)` followed by the
  inclusion of `Ae` into `A`, as an additive map.
- `coordinateKernel e` is the kernel of `coordinate e`, the source's
  `Ā(1-e) = {x | x(e) = 0}`.
- `coordinateEntourage e` is `{(x, y) | x(e) = y(e)}`.

Family coherence `x(f) e = x(e)` for `e ≤ f` proves that kernels and
entourages are antitone in the corner order (`coordinateKernel_antitone`,
`coordinateEntourage_antitone`). Vanishing or equality at `f` descends to
`e` after right multiplication by `e`. `coordinateEntourage_eq_kernel`
identifies each entourage with the pairs whose difference lies in the
kernel. Under `IsIdempotented A`, a common upper idempotent of `e` and `f`
gives `coordinateKernel_common_refinement`. Hence the entourages are
directed downwards (`coordinateEntourage_directed`).

`uniformSpace A` is defined as the infimum over all actual
`e : Idempotent A` of the pullbacks of the discrete uniformity on `A`
along `x ↦ x(e)`. It is a definition, installed locally with `let`, and
not a global instance. The construction has no topology parameter,
replacement family space or assumed compatibility certificate.

## Bases

`uniformity_eq` computes the uniformity filter as the infimum of the
principal filters of the coordinate entourages. It uses Mathlib's
formulas for the uniformity of an infimum and of a pullback, and the
diagonal uniformity of `⊥`. Under `IsIdempotented A`, directedness and
Mathlib's basis theorem for directed infima of principal filters give
`uniformity_hasBasis`: the single-coordinate entourages form an exact
basis of the uniformity. The zero idempotent makes the index type
nonempty. The neighborhood basis from a uniformity basis then gives
`nhds_hasBasis`: at every family `b`, the fibers `{x | x(e) = b(e)}` form
an exact neighborhood basis.

`coordinate_fiber_eq_translate` writes each fiber as
`{x | x - b ∈ coordinateKernel e}`. `coordinate_fiber_eq_image_add`
writes it as the translate `b + Ā(1-e)`, the image of the kernel under
`k ↦ b + k`, which is the source's left-translation form.
`nhds_hasBasis_translate` restates the neighborhood basis with these
translates. At `b = 0` the fibers are exactly the kernel carriers, giving
`nhds_zero_hasBasis`.

## Group, product comparison and separation

`uniformContinuous_coordinate` follows directly from the defining
infimum: each coordinate is uniformly continuous into discrete `A`.
Each coordinate is an additive homomorphism, so Mathlib's pullback
theorem for uniform additive groups gives a uniform additive group on
each pulled-back uniformity. The infimum theorem for uniform additive
groups then proves `uniformAddGroup` for the actual pointwise group.
This holds for every nonunital ring.

`discreteProductUniformSpace A` is the product uniformity on the full
function type `Idempotent A → A`, each factor discrete, with no
compatibility restriction. The product uniformity formula, commutation of
pullback with infima, and composition of pullbacks prove
`uniformSpace_eq_product_comap`: pulling back the product uniformity
along the actual inclusion `x ↦ x.val` gives exactly `uniformSpace A`.
`uniformSpace_eq_subtype` states the same equality with Mathlib's
subtype uniformity, with discrete uniformity installed on `A`. A
following check confirms that the instance found there is
`instUniformSpaceSubtype` on the full discrete product.
`isUniformEmbedding_val` adds injectivity of `Subtype.val`. The discrete
product and its subspaces are Hausdorff, so the same equality proves
`hausdorff` for every nonunital ring. These comparisons prepare a
separate closedness and completeness argument.

## The canonical map

The published canonical additive map `canonical : A →+ Ā` has
coordinates `a ↦ a * e`. Pulling the defining infimum back along it,
commuting pullback with infima and composing pullbacks gives exactly
the defining infimum of the published `idempotentedRingUniformSpace A`.
This is `comap_canonical`. The proof is definitional after these
rewrites; it uses no compatibility certificate. It gives
`isUniformInducing_canonical` for every nonunital ring. Under
`IsIdempotented A`, the published algebraic injectivity
`canonical_injective` gives `isUniformEmbedding_canonical`. This makes
precise the source's continuous canonical embedding.

## Interfaces and scope

Complete unapplied `example` checks cover each public definition and
theorem at an arbitrary universe `uA`. No hypothesis of a global unit,
commutativity, nontriviality or countability is used, and zero rings
are allowed. Only the basis theorems and the uniform embedding of
`canonical` assume `IsIdempotented A`.

The entourage and neighborhood bases are the source's construction.
The exact uniform embedding, the discrete-product and subtype
comparisons, and the Mathlib uniform-group and Hausdorff formulations are
internal consequences of it, not numbered results of Renard. This module
does not prove density, completeness, that `Ā` is a uniform
completion, continuity of the limit multiplication, or the extension
of module actions; those remain separate tasks.
