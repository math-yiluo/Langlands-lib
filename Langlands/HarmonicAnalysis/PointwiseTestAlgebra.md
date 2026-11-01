# Compact-clopen indicators and finite local units for pointwise tests

This module completes the pointwise test-function algebra in the namespace
`Langlands.HarmonicAnalysis.PointwiseTestAlgebra`. It imports
`PointwiseTestAlgebraCore`, which constructs the actual compact-support
nonunital subalgebra of locally constant complex functions, its faithful
inclusion, its value-preserving comparisons with the published vector
and scalar test spaces, and its ambient smooth-function action.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.4–II.2.5, printed
pp.38–40 / PDF44–46. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The complete surrounding PDF44–48 was read. II.2.4 describes the
pointwise algebra and its compact-open idempotents; II.2.5 uses their
inclusion and intersection relations and, on printed p.40, their
binary-union inclusion-exclusion formula.

## Actual indicators and their relations

For explicit witnesses that `U` is clopen and compact, `characteristic`
is its actual indicator function, equal to one on `U` and zero outside.
It is obtained from `Hecke.TestFunction.characteristic` using the inverse
scalar equivalence. `scalarEquiv_characteristic` records agreement as
an equality of bundled scalar test functions; `inclusion_characteristic`
records agreement with `LocallyConstant.charFn`. Its function support
is exactly `U`, including when `U` is empty.

`characteristic_mul` proves that the product of two indicators is the
indicator of their intersection. The intersection is compact because
one set is compact and the other is closed; this argument does not need
Hausdorffness. Pointwise evaluation also proves idempotence.
`characteristicIdempotent` packages the resulting element in the
public `Langlands.Algebra.Idempotent` type with its corner order.

The two `characteristic_mul_eq_self_iff` and
`mul_characteristic_eq_self_iff` lemmas characterize fixing an arbitrary
test on either side by the containment of its actual support in `U`.
They follow by evaluating the equality outside `U` and, conversely,
using that the test vanishes there. For nested compact-clopen sets,
`characteristic_mul_of_subset` gives the absorption identity and
`characteristicIdempotent_le` gives the corresponding corner-order
relation.

`characteristic_empty` is zero.
`characteristic_union` is the source identity
\(\chi_{U\cup V}=\chi_U+\chi_V-\chi_{U\cap V}\).
`characteristic_union_disjoint` removes the intersection term for
disjoint sets. These formulas are proved by the four membership cases
at each point.

`finiteUnionCharacteristic` is the indicator of the finite union of
any family of compact-clopen sets. Its evaluation formula and empty
case are explicit. `finiteUnionCharacteristic_insert` gives the
insertion recurrence
\[
 \chi_{\bigcup_{j\in \{i\}\cup s}U_j}
 =\chi_{U_i}+\chi_{\bigcup_{j\in s}U_j}
   -\chi_{U_i}\chi_{\bigcup_{j\in s}U_j}.
\]
It does not require the inserted index to be new.
`finiteUnionCharacteristic_mul` shows that the union indicator fixes
every member indicator. Finite unions therefore supply upper bounds
for the source system, with no nonempty-family restriction.

## Intrinsic finite local units

`finiteSupport s` is the finite union of the actual supports of the
tests in `s`. Each support is compact and clopen by the published
scalar test-function lemmas transported through the value-preserving
equivalence. Finite unions retain both properties.

`localUnit s` is the characteristic function of this specified set.
Its support and idempotence are proved, and the local unit of the
empty family is zero. Since each member support lies in the union,
`localUnit_mul` and `mul_localUnit` prove that this one characteristic
idempotent fixes every member on both sides.
`exists_characteristic_local_unit` exposes the compact-clopen set and
both fixing identities. `isIdempotented` applies the public
`Langlands.Algebra.IsIdempotented.iff_two_sided_local_units` theorem to
these constructed indicators; it assumes no separate local-unit
or idempotented-ring hypothesis.
`finite_family_local_unit` supplies the same characteristic conclusion
for every finite index type in an independent universe.

This direct finite-union-of-supports argument is the implemented
derived proof of the source assertion. It works for every supplied
topology on an arbitrary `X : Type uX`, without separation, local
compactness, countability, or nonemptiness. It preserves zero tests,
empty sets, empty index types and empty spaces.

For the source convention, a t.d. space is Hausdorff with a compact-open
neighborhood basis. In a Hausdorff space, a compact set is closed, so a
compact open is clopen. `characteristicOfCompactOpen` provides this
specialization and its unchanged pointwise formula. The Hausdorff
assumption is confined to that specialization.

The construction ends at the pointwise algebra, its smooth
multipliers, characteristic idempotents, directed finite-union laws
and intrinsic finite local units. Global unitality criteria, extension
of other nondegenerate module actions and the actual sheaf/module
equivalences are separate tasks. In particular, this module makes no
identification between ordinary nondegeneracy over the unital ambient
smooth algebra and the source convention relative to compact-open
indicators.
