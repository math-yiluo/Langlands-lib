# Proof of the DVR ramification-inertia lower degree bound

`Langlands.LocalField.dvrDegreeLowerBound` proves exactly the published
proposition `Langlands.LocalField.DVRDegreeLowerBound`, imported unchanged from
`Langlands.LocalField.DVRDegreeStatement`. Its universe parameters are
`uR`, `uS`, `uK`, and `uL`, independently. With the rings, fraction fields,
local algebra map, compatible scalar towers, and finite field-extension
hypothesis quantified in that proposition, it proves

`(maximalIdeal S).ramificationIdx R * (maximalIdeal S).inertiaDeg R ≤ finrank K L`.

This is an internal derived proof by Worker 109. The statement was isolated
from the completed-local-degree project by Worker 107 and formalized in its
separate published statement module. The proof here is developed from the
pinned Mathlib module, localization, and length APIs; it does not transcribe an
external literature proof. Both auxiliary theorems are private implementation
lemmas in this file.

## Bounding the quotient dimension

The helper `quotient_dimension_bound` works over a principal ideal domain `R`
with fraction field `K`. It takes a torsion-free `R`-module `M`, an injective
`R`-linear map from `M` into a finite-dimensional `K`-vector space `V`, and a
surjective `R`-linear map from `M` to a `k`-vector space `Q`, where `k` is a
field with compatible `R`-action. It proves `finrank k Q ≤ finrank K V`.

If `Q` is not finite-dimensional, Mathlib's natural-number `finrank` is zero,
and the bound follows immediately. Otherwise choose a finite basis of `Q`
and lift its vectors to `M`. Their `R`-span `N` is finitely generated and
inherits torsion-freeness. Mathlib's PID freeness instance supplies a basis
of `N`. Its images in `Q` span over `k`: each chosen lifted vector can be
expanded in the basis of `N`, and mapping that expansion gives its original
basis vector of `Q`. Thus `finrank k Q` is at most the size of this basis of
`N`.

The same basis maps injectively into `V` and stays linearly independent over
`R`. `LinearIndependent.iff_fractionRing` upgrades that independence to `K`.
Its cardinality is therefore at most `finrank K V`, giving the bound. Only
`N`, the span of finitely many chosen lifts, needs to be finite over `R`.

## Identifying the current ramification and inertia product

The helper `ramification_inertia_eq_quotient_finrank` applies to a local
algebra map between commutative local rings. Put `p = maximalIdeal R` and
`q = maximalIdeal S`. It proves

`q.ramificationIdx R * q.inertiaDeg R = finrank (R ⧸ p) (S ⧸ pS)`,

where `pS = p.map (algebraMap R S)`.

Locality gives the required lies-over instance. The complement of `q`
consists of units, so `IsLocalization.atUnits` identifies `S` with its
localization `Sq` at `q`. The induced algebra equivalence on quotients,
together with invariance of module length under a surjective scalar map,
identifies the current `q.ramificationIdx R` with
`(Module.length S (S ⧸ pS)).toNat`. This uses
`Ideal.ramificationIdx_eq` directly, without passing through the deprecated
ramification invariant.

`Ideal.inertiaDeg_eq_of_isMaximal` identifies the current inertia degree with
`finrank (ResidueField R) (ResidueField S)`. Next,
`IsLocalRing.length_restrictScalars` gives

`length R (S ⧸ pS) = length S (S ⧸ pS) * length (ResidueField R) (ResidueField S)`.

Since `R → R ⧸ p` is surjective, the left side equals
`length (R ⧸ p) (S ⧸ pS)`. Applying `ENat.toNat`, using its multiplicativity,
and using `Module.length_eq_rank` and `Cardinal.toNat_toENat` turns the
length identity into the asserted product identity. This argument does not
assume the lengths or the residue extension are finite; the conversions use
Mathlib's existing conventions for infinite cardinality and length.

## Closing the published proposition

The final theorem introduces precisely the parameters and hypotheses of
`DVRDegreeLowerBound`. The tower `R → K → L` makes `L` torsion-free over
`R`. The fraction-ring map `S → L` is injective, so torsion-freeness pulls
back to `S`. Apply the dimension helper with `M = S`, `V = L`,
`k = R ⧸ maximalIdeal R`, and `Q = S ⧸ pS`; the quotient map supplies its
surjection and `S → L` its injection. The product identity then gives the
required inequality.

The proof adds no hypothesis to the published proposition. In particular,
it does not assume `Module.Finite R S`, completeness, separability, or a
degree identity. It uses no proof holes or new axioms. Comparisons with
global prime invariants and completed local fields remain outside this
module, as in the statement's scope.
