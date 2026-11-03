# Finite freeness of the actual rational-character valuation image

Author: Worker 200.

This derived construction gives a finite integer basis of the actual
rational-character valuation image and identifies its character groups,
with compact-open topology, with finite products of their target group.
For every actual connected reductive group it gives coordinates in
`(ℂˣ)^r` and `Circle^r`, where `r` is the rank of that actual image.

## Sources and provenance

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
edition, V.2.2–V.2.4, printed pp.105–106 (PDF pp.111–112), defines rational
characters, the integer valuation homomorphism `H_G`, its image `Λ(G)`,
and characters of that image. V.2.4 observes that `Λ(G)` is free of finite
rank and uses it to describe unramified characters as a complex torus.
Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The Lean file supplies an integer-dual proof of finite freeness and a
chosen-basis description of the compact-open character groups. The
topological argument is an internal deduction using Mathlib, rather than
a formalization of the group-algebra spectrum argument in V.2.4. It
imports the actual valuation image from
`Langlands.Representation.Plancherel.RationalImageCharacters` and the
published theorem `Langlands.GroupScheme.rationalCharacterLattice` from
`Langlands.GroupScheme.Rational.CharacterLatticeProof`. No new group or
character-lattice framework is introduced.

## Actual image and finite freeness

The field `F : Type u` is an arbitrary nonarchimedean local field, in any
characteristic. Initially `G` is any actual group scheme over `Spec F`.
The group `rationalDiscreteValuationImage G` is the discrete copy of the
range of `rationalCharacterValuation G`. It is the actual range, without
an assumption that every integer-valued functional is attained.

`rationalImageIntegerDual G` sends an element of the additive version of
this image to its integer-linear functional on
`GroupScheme.rationalCharacters G`. Its evaluation formula is
`rationalImageIntegerDual_apply`. Extensionality of the range subtype and
of additive homomorphisms proves `rationalImageIntegerDual_injective`.
The integer dual is torsion free, so this injection gives the instance
`rationalImage_isTorsionFree`, without a finiteness premise.

The generic finite construction assumes only
`Module.Finite ℤ (GroupScheme.rationalCharacters G)`. The integer dual of
a finite module is Noetherian: Mathlib's `isNoetherian_linearMap` applies
over the Noetherian ring `ℤ`. An injection into that dual therefore gives
the instance `rationalImage_moduleFinite` by
`Module.Finite.of_injective`. The finite torsion-free module over the
integer PID is free, using the instances from
`Mathlib.LinearAlgebra.FreeModule.PID`.

`rationalImageRank G` is the natural-number `Module.finrank` of the
additive image. Under character finiteness,
`rationalImageBasis G` uses `Module.finBasis` to choose an integer basis
indexed by `Fin (rationalImageRank G)`. This basis is noncanonical.
The rank-zero case is included.

## Character coordinates and topology

For a commutative group `B : Type v` with a topology,
`rationalImageCharacterOfCoordinates G c` reconstructs a character from
values `c : Fin (rationalImageRank G) → B`. It uses the basis's linear
extension into `Additive B`, whose canonical integer module structure is
available for every commutative group. The source is discrete, so the
reconstructed homomorphism is continuous.

`rationalImageCharacterOfCoordinates_basis` proves its value at each
basis element is the specified coordinate.
`rationalImageCharacterOfCoordinates_apply` proves the exact formula

```text
χ_c(a) = ∏ i, c(i) ^ ((rationalImageBasis G).repr (Additive.ofMul a) i).
```

The exponents are integers, so this is a finite Laurent monomial. The
formula follows from `Module.Basis.constr_apply_fintype` and the
conversion of additive sums and integer scalar multiples into products
and integer powers.

When `B` is a Hausdorff topological group,
`rationalImageCharacterCoordinates G` is the multiplicative equivalence
from continuous characters of the image to these tuples, given by
evaluation on the basis. Its inverse is the reconstruction above. The
two inverse laws use `Module.Basis.constr_self` and the basis evaluation
formula, and multiplication is pointwise.

`rationalImageCharacterContinuousCoordinates G` upgrades this to a
continuous multiplicative equivalence for the existing compact-open
topology. The forward map is continuous coordinatewise evaluation. For
the inverse, the closed evaluation embedding of continuous homomorphisms
from a discrete group into the function product reduces continuity to
each evaluation. The finite Laurent formula then reduces it to
continuity of integer powers and finite products. The theorem
`rationalImageCharacterContinuousCoordinates_apply` records that the
forward map is exactly basis evaluation.

## Connected reductive specialization and scope

For `hG : GroupScheme.IsConnectedReductive G`, the published
`GroupScheme.rationalCharacterLattice F G hG` proves that the actual
rational-character module is finite and free. Its finiteness component
discharges the generic construction's premise.
`rationalReductiveImage_free_finite` consequently proves both freeness
and finite generation of the actual valuation image.

`rationalReductiveImageCharacterCoordinates G hG` gives

```text
rationalImageCharacters G ≃ₜ* (Fin (rationalImageRank G) → ℂˣ).
```

`rationalReductiveUnitaryImageCoordinates G hG` gives the corresponding
equivalence from `rationalUnitaryImageCharacters G` to
`Fin (rationalImageRank G) → Circle`. These groups are the published
complex and circle-valued duals of the actual image. Their topology is
unchanged. Both equivalences retain arbitrary field universes and
characteristics, including nonsplit connected reductive groups.

This unit does not yet compose these coordinates with the published
comparison to unramified characters on rational points. It does not
identify the image rank with the rational-character rank, prove finite
index in the entire integer dual, compare with a split component, or
construct a group scheme or an analytic manifold structure on the
character group. Haar normalization, twist orbits and the
representation-theoretic and Plancherel conclusions remain separate.
