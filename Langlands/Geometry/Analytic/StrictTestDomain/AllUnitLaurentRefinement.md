# All-unit standard covers and Laurent refinement

Author: Worker 105.

This module constructs a finite Laurent refinement of the standard rational
cover associated with a finite tuple of units. All declarations are in
`Langlands.Analytic.StrictTestDomain.RationalData`. The scalar field `K : Type u`
is an ultrametric normed field; the quotient constructions and the cover results
assume `CompleteSpace K`. Both source and target are actual
`PresentedStrictAffinoidAlgebra K` objects. The construction works for every
universe `u`.

## Source and translation

The source is Piotr Achinger, *Introduction to non-Archimedean Geometry*,
November 22, 2020, p.67, the all-unit case in the proof of Theorem 7.0.1.
The registered source is `achinger-2020-non-archimedean-geometry-nov22`,
SHA256 `666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
That argument forms Laurent domains for the ratios of the tuple entries so
that each resulting domain lies in one standard rational domain. This file
makes the finite family, its choice of standard domain, and its actual quotient
maps explicit. The Boolean selector and the empty-tuple convention are derived
implementation choices, rather than quoted definitions.

The imported `IteratedLaurentCover` construction supplies actual rational
presentations for finite intersections of Laurent domains, with quotient
comparisons and recursive binary-branch equivalences. Its convention is retained:
`false` selects the upper bound `x g ≤ 1`, and `true` selects the lower bound
`1 ≤ x g`. The imported pairs are unchanged.

## Ratios, indices, and the chosen standard domain

For `f : Fin n → P`, `allUnitRatios f` lists all `n * n` ordered ratios
`f i * Ring.inverse (f j)`, using `finProdFinEquiv` to identify the index with
`Fin (n * n)`. The definition is total, but the comparison and refinement
theorems use `hu : ∀ j, IsUnit (f j)`.

`AllUnitLaurentIndex n` is the subtype
`{ε : Fin (n * n) → Bool // 0 < n}`. It is finite by the existing finite-function
and subtype instances. For positive `n` it retains every Boolean leaf,
including leaves with empty loci. `allUnitLaurentLeaf f a` is exactly
`iteratedLaurent (allUnitRatios f) a.val`, with its chosen rational datum and
actual quotient algebra. Its membership condition is therefore the conjunction
of the selected bounds for all ordered ratios.

`allUnitLaurentStep ε i j` selects `i` when the comparison of `f i / f j`
is a lower branch, and selects `j` for an upper branch. The definition
`allUnitLaurentIndex a : Fin n` folds that step over `List.finRange n`, starting
at zero, whose validity is supplied by `a.property`. This selector depends only
on the Boolean choices and the fixed finite enumeration, independently of any
point in the leaf.

The proof `allUnitRatio_choice_bound` multiplies the chosen ratio inequality by
the nonnegative number `x (f j)`. Multiplicativity and the unit inverse identity
give

`x (f i * Ring.inverse (f j)) * x (f j) = x (f i)`.

Thus the selected candidate dominates both inputs. The internal induction
`foldl_dominates` shows that the final candidate dominates every tuple entry.
Consequently `allUnitLaurentInclusion f hf hu a` is an actual rational-domain
inclusion

`allUnitLaurentLeaf f a ⟶ standardRational f hf (allUnitLaurentIndex a)`,

where `hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0` is the standard tuple's
no-common-zero hypothesis. The theorem `allUnitLaurent_covers` supplies a leaf
through every spectrum point, using `hf` to establish positive tuple length
and the imported finite Laurent cover theorem. `allUnitLaurent_familyCovers`
packages the same coverage with indices lifted by `ULift.{u}` to the universe
of the rational site.

## Actual maps and base change

The inclusion induces the existing bounded restriction from the selected
standard quotient to the leaf quotient. Its structural-map equation is
`allUnitLaurentInclusion_comp_baseMap`.

For any actual bounded algebra map `φ : BoundedAlgHom K P Q`,
`allUnit_tuple_units_pullback` preserves the unit hypothesis and
`allUnitRatios_map` identifies the mapped ratio tuple with the ratio tuple of
the images. The proof of the latter transports the inverse using unit
cancellation. `locus_allUnitLaurent_pullback` then identifies the pulled-back
leaf locus with the leaf of the mapped tuple.

`allUnitLaurentPullbackIso` is the resulting isomorphism in the category of
rational data. It retains the two chosen presentations; it does not assert
that those presentations are equal. `allUnitLaurentComparison` composes the
original leaf's actual pullback comparison with the inverse isomorphism's
restriction, obtaining a bounded algebra map between the actual leaf quotients.
Its equation over the base is `allUnitLaurentComparison_comp_baseMap`.

The theorem `allUnitLaurentComparison_restriction` asserts equality of the two
bounded maps from the original selected standard quotient to the mapped leaf
quotient: restrict after the standard comparison, or compare after the original
restriction. The selected standard datum for the mapped tuple is definitionally
the pullback of the original standard datum, and its selected index is the same
`allUnitLaurentIndex a`. The proof uses the standard quotient's `hom_ext`,
the two restriction structural-map identities, and the leaf comparison
structural-map identity. These are equations of the actual quotient maps,
rather than only equations of spectrum loci.

## Empty tuple and scope

At `n = 0`, `allUnitLaurentIndex_zero_empty` proves that the refinement index
type is empty, so no index of `Fin 0` is invented. The hypothesis `hf` then
forces `P` to be a zero algebra in the sense `Subsingleton P`:
`subsingleton_of_empty_tuple` argues that a nonzero presented strict affinoid
has a spectrum point, where `hf` would supply an impossible element of
`Fin 0`. The coverage theorem remains valid in this case because the spectrum
is empty. The underlying general iterated Laurent construction still uses
`whole` for an empty ratio tuple; the refinement simply retains no indexed
leaf at `n = 0`.

No nontriviality or reducedness assumption is imposed on the base algebras,
and empty leaves are preserved. Trivial scalar valuations are also allowed:
only order comparisons, multiplicativity, unit identities, and the imported
rational quotient properties enter these arguments. The nontrivial valuation
standing assumption in the source is unnecessary for this limited construction.
The all-unit assumption remains essential to the stated ratio comparison
argument. This module constructs a refinement and quotient-map comparisons;
it asserts no scalar gluing, scalar descent, or sheaf theorem.
