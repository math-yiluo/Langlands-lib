# Finite local ramification and conductor expressions in every characteristic

Worker 845 generalizes the published integer-ring action and lower filtration
from `Ramification.Galois`. The declarations are in
`Langlands.Ramification.Local`. They use a supplied
`T : Langlands.LocalField.TopologicalData K₀ L`, a field `K` and a scalar tower
`K₀ → K → L`. The base has a specified topology and valuative relation.
The supplied extension is a nonarchimedean local field with the base module
topology and extending valuative relation. No characteristic hypothesis is
made. The base, intermediate and extension universes are independent.

`integerAutomorphism T K σ` restricts a `K`-automorphism of `L` to the actual
integer ring `T.Integers`. The restriction is constructed, not assumed:
`σ` and its inverse are linear over `K₀`, hence continuous for the supplied
module topology. In a nonarchimedean local field, valuation strictly less
than one is equivalent to powers tending to zero. If the image of an integral
element had valuation greater than one, continuity of the inverse applied to
powers of its inverse would contradict integrality. This proves stability
in both directions and supplies the ring equivalence.

`integerAutHom` packages composition, and `integerAction` is the explicit
resulting ring action. `residueHom` applies the actual local residue-field
functor. Its kernel is `inertia`. `lowerRamificationGroup T K i` requires
`σ(x) - x ∈ m^(i+1)` for every element of that same integer ring.
`lowerRamificationGroupInt` puts the full group at all negative indices.
The membership lemma, normality and antitonicity follow from the published
characteristic-free generic `lowerGroup` construction. Applying the residue
quotient to `σ(x)-x` proves `lowerRamificationGroup_zero = inertia`.

For termination assume `[FiniteDimensional K₀ L]`. Restriction of scalars
makes `L` finite over `K`, hence its automorphism group is finite. The supplied
local-field integer ring is Noetherian and has fraction field `L`. Equality
of automorphisms on this ring therefore implies equality on `L`, proving
faithfulness. These facts discharge the generic lower-filtration termination
theorem. They do not require perfectness, separability or characteristic zero.

The finite-dimensional conductor expressions use the published rational sums
of fixed-space codimensions. `artinConductor` sums from index zero with
weight `|G_i|/|G_0|`; `swanConductor` omits index zero. These are expressions
for representations over any field, without an integrality assertion.
`inertiaIntegerAction` restricts the same actual action to inertia, and
`inertiaLowerGroup` views the same lower groups as subgroups of inertia.
Its zeroth group is the whole inertia group. Thus the inertia Artin/Swan
expressions apply without extending an inertia representation to the full
automorphism group, and their tame term is `dim V - dim V^I`.
All four expressions are invariant under representation equivalence by the
existing generic fixed-space equivalences.

`descendInertiaRepresentation` takes a specified surjective group map `π`
to this inertia group and a representation whose kernel contains `ker π`.
It descends the units-valued representation through Mathlib's
`liftOfSurjective`, then includes the units in linear endomorphisms.
The evaluation formula and uniqueness follow from surjectivity.
`artinConductorOfQuotient` and `swanConductorOfQuotient` evaluate the same
inertia expressions on that descent. They assert neither existence of a
suitable quotient nor independence of its choice.

For finite Galois extensions of local fields these are Serre's usual lower
groups. The code also constructs groups for nonnormal finite extensions;
no arithmetic quotient or extension-independence theorem is claimed there.

## Sources and provenance

Serre, *Local Fields* (1979), IV §1, Lemma 1 and Proposition 1, printed
pp.61–62 (PDF pp.68–69), defines these congruence groups, inertia at zero,
normality, decrease and eventual triviality. VI §2, Proposition 2 and
Corollary 1′, pp.100–101 (PDF pp.107–108), gives the weighted codimension
formula. The passages were read in the retained original:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The registered 2019 author corrections, PDF pp.2–3, were checked; their
nearby p.63 correction does not alter the definitions used here.
The Swan expression is the positive-index part of the same published
project sum. The supplied-data interface and quotient-descent packaging
are internal constructions. Proofs of eventual triviality use the
Noetherian-ring generic result rather than a chosen ring generator.

## In-place p-adic specialization

In this table the first column has prefix `Langlands.Ramification.Local`
and the second `Langlands.Ramification.Padic`. Substitute
`K₀ = Padic p`, `L = F.Carrier`, and use `T.toLocalData` in the first column.
All original p-adic declaration names, types and meanings are retained.

| General declaration | Existing p-adic specialization |
| --- | --- |
| `integerAutomorphism T.toLocalData K` | `integerAutomorphism T K` |
| `integerAutHom T.toLocalData K` | `integerAutHom T K` |
| `integerAction T.toLocalData K` | `integerAction T K` |
| `residueHom T.toLocalData K` | `residueHom T K` |
| `inertia T.toLocalData K` | `inertia T K` |
| `lowerRamificationGroup T.toLocalData K` | `lowerRamificationGroup T K` |
| `lowerRamificationGroupInt T.toLocalData K` | `lowerRamificationGroupInt T K` |
| `inertiaIntegerAction T.toLocalData K` | `inertiaIntegerAction T K` |
| `inertiaLowerGroup T.toLocalData K` | `inertiaLowerGroup T K` |
| `artinConductor T.toLocalData K` | `artinConductor T K` |
| `swanConductor T.toLocalData K` | `swanConductor T K` |
| `inertiaArtinConductor T.toLocalData K` | `inertiaArtinConductor T K` |
| `inertiaSwanConductor T.toLocalData K` | `inertiaSwanConductor T K` |
| `descendInertiaRepresentation T.toLocalData K` | `descendInertiaRepresentation T K` |
| `artinConductorOfQuotient T.toLocalData K` | `artinConductorOfQuotient T K` |
| `swanConductorOfQuotient T.toLocalData K` | `swanConductorOfQuotient T K` |

Each elementary lemma specializes with the same leaf name and `T.toLocalData`.
The existing p-adic integer automorphism directly calls the general one.
The composite p-adic expressions keep their original outer bodies so that
published explicit `unfold` proofs continue working; their components reduce
to exactly the general definitions. In particular this is definitional
agreement, including the entire action structure, not a comparison theorem
between two filtrations. All original statement text is unchanged.

A private diagnostic reproduces every original public declaration in a
separate namespace and checks equality of the complete unapplied declarations
by `rfl`; this checks both their full types and their defining values.
The finite source and these checks compile. The companion
[`Herbrand/GeneralFinite`](Herbrand/GeneralFinite.md) describes the direct
Mathlib-local-field realization, characteristic audit and broader consumer
checks. Independent review and publication remain separate.
