# Collection for positive chamber root groups

`KPApartmentData.positiveChamberProductSubgroup` is the subgroup whose carrier is
exactly the range of the published `orderedChamberBlockProduct`, for any supplied
finite enumeration of the indivisible roots positive on a cocharacter `ν`.
The factors retain their published doubled-root blocks and their supplied order.
The carrier equals both the supremum of **all** positive actual root groups and
the subgroup closure of their union. Thus the product is closed under
multiplication and inversion and its range is independent of the enumeration.
Repeated entries are permitted; no coordinate uniqueness is claimed here.

The construction works over a field `k : Type u` for arbitrary `u`, with the
published `D : KPApartmentData i ω`, monomorphism and affine-group hypotheses.
It takes two explicit apartment-root assumptions: the extended affine roots
form `IsAffineRootSystemWithRankZero`, and their derivative set equals the range
of the actual apartment `rootForm i`. These are the existing AS 2 and derivative
comparison clauses, not an added Iwahori factorization hypothesis. No chamber
condition on `x` is needed. `strict = false` means depth `0`; `strict = true`
means depth `0+`. Both choices are proved at every apartment point.

## Sources and scope

This is a derived supporting construction for the chamber Iwahori proof.
Its source motivation is the subgroup and order-independence assertion of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 7.3.11(2),
printed p. 249 / PDF p. 280, and its use in Proposition 7.3.12, printed p. 250 /
PDF p. 281. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The book's statement allows closed positive subsets and general concave depth
functions. This module proves the full positive set at the two constant zero
depths used by the current chamber target; it does not claim that generality.
It also does not prove Proposition 7.3.12's bijections.

The authors' corrections of 1 November 2024 are registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
Corrections PDF p. 33 adds AS 5 to the Chapter 7 assumptions and PDF pp. 33–34
adds the positive-central-depth mixed-order assertion to Proposition 7.3.12.
Neither addition is inferred from this supporting collection result. The full
host target keeps its original assumptions and remains a separate obligation.

The implemented proof derives its bounds directly from the published
`KPApartmentData` valuation axiom V3, affine-root coroot integrality, the actual
root-ray descent in `Rational.RootRayDecomposition`, and V4's doubled-root
inclusions from `ChamberFiltration`. It uses the generic finite group argument
in `GroupTheory.HeightCollection`. The intermediate multiplicity and height
lemmas and the carrier-copy construction are internal consequences of those
interfaces; they are not asserted to be additional literal statements of the
book. No reducedness or separate relative-root-system realization is assumed.

## Implemented argument

`rootForm_nsmul` proves that the apartment form of an actual root `m • a` is
`m` times the apartment form of `a`. It descends to representatives in the
apartment-vector quotient and evaluates the tensor pairing. For roots `a` and
`m • a`, with `m > 0`, the derivative comparison supplies extended affine roots
with those derivatives. A coroot for the latter evaluates it to two, while
AR 3 makes its evaluation on the former an integer `z`. Consequently `m*z = 2`.
Positivity of `m` forces `z > 0` and `m ≤ 2`, proving
`root_multiple_eq_one_or_two`. Combining this with the imported descending
root-ray argument proves `exists_indivisiblePositiveRoot_eq_or_double`:
every positive actual root is an indivisible positive root or its double.
This does not require injectivity of `rootForm`.

`positiveRoots_nonopposite` evaluates an alleged negative proportionality on
`1 ⊗ ν`; the two positive pairings contradict it.
`positiveRootCombination_height` shows that the pairing of a root `p*a + q*b`,
for positive integers `p,q` and positive roots `a,b`, is positive and strictly
larger than each input pairing. Converting these positive integer pairings to
natural numbers supplies the finite collection heights.

`filtration_commutator_le` rewrites V3's closures of actual subgroup carriers
as subgroup suprema. `chamberRootGroup_commutator_height` then bounds the
commutator of two positive zero-depth groups by all root groups of strictly
larger height. At depth `0+`, each input element is first put into some real
filtration of positive depth. These filtrations form a directed union; V3
places each output at positive depth `p*r + q*s`. Thus the same height bound
holds at depth `0+`, including equal input roots. The accompanying
`range_orderedPositiveRootGroupProduct_eq_iSup` applies generic height collection
to any complete finite enumeration of all positive actual roots, without the
AS 2 assumptions needed for primitive-root compression.

For the prescribed indivisible-root enumeration, the main collection proof
inserts a doubled-root position immediately after each primitive-root position.
The auxiliary family is indexed by `Fin (n * 2)` via `finProdFinEquiv`.
An absent double has the bottom subgroup in its position. The root-multiplicity
lemma ensures that every positive output root in V3 occurs in this enlarged
family at its actual height. Generic height collection therefore identifies
its ordered-product range with its subgroup supremum. A private list-product
identity groups the adjacent positions without commuting any factors.
V4 puts each doubled-root subgroup inside its parent at both zero depths, so
multiplying each pair compresses the product back to the given primitive-root
order. Conversely, a primitive-root tuple expands by inserting identities in
the doubled positions. The enlarged supremum is the supremum over all positive
roots. This proves
`range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup`.

`range_orderedPositiveChamberBlockProduct_eq_iSup` transports that result through
the point-preserving `chamberRootBlockEquiv`, so its left side is the range of
the original published block map. The corresponding `eq_closure` theorem
rewrites the supremum as the closure of the union. The specialization
`range_orderedPositiveChamberBlockProduct_zero_eq_closure` states this directly
with `D.filtration x b 0`, for use by the sharp range argument.

`positiveChamberProductSubgroup` uses `Subgroup.copy` to give the actual block
range as its membership predicate. `mem_positiveChamberProductSubgroup` is the
definitional tuple-existence equivalence, and
`positiveChamberProductSubgroup_eq_iSup` identifies it with the generated
positive-root subgroup. Finally,
`range_orderedPositiveChamberBlockProduct_order_independent` compares any two
finite enumerations of the same indivisible positive root set through that
common supremum. Empty families are included.

These results supply collection and subgroup structure only. They do not
identify this subgroup with a sharp or full unipotent intersection, prove
injectivity of its coordinates, introduce a central factor, prove a facet
factorization, or establish the full chamber Iwahori decomposition.

The adjacent-pair identity `prod_ofFn_pairs` is public for reuse by the positive-depth ray compression module. Its statement and proof are unchanged.

The public helper `range_orderedProduct_pairs` absorbs each adjacent
pair of subgroup factors when the first equals the target factor and the
second is contained in it. Its unchanged argument is also reused for
selected-root depth collection.
