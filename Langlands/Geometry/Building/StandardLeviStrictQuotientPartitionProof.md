# The partition of the nonnegative quotient by actual standard-Levi pieces: proof

`Langlands.GroupScheme.CocharacterUniformizer.standardLeviStrictQuotientPartition`
proves the published
`Langlands.GroupScheme.CocharacterUniformizer.StandardLeviStrictQuotientPartitionStatement`
exactly, at its universe parameter `u` and with all its hypotheses: every
nonarchimedean local field `F`, connected reductive actual group scheme `G`,
actual maximal split torus `i : T → G`, generic cocharacter `ν`, actual split
component `a₀ : A₀ → G` and compatible morphism `f₀ : A₀ → T` with
`f₀ ≫ i = a₀`. No further premise is added. The module has three
declarations.

## Identification of each piece

`standardLeviStrictQuotientFace_eq_uniformizerImage_of_strictImage` assumes
the exact proposition `StandardLeviStrictImageStatement` and proves that the
actual strict piece `standardLeviStrictQuotientFace F i ν A₀ f₀ J` equals the
image, in `T(F)/f₀(C_{A₀})`, of the common-uniformizer points of the standard
integral cocharacters `IsStandardCocharacter i ν J`.

- Forward inclusion: membership in the piece supplies an actual closed
  standard-Levi representative, its actual split component, a compatible map
  into `T` and a strict common-uniformizer point. The strict-image
  proposition at that representative rewrites the point as the
  uniformizer image of a standard cocharacter.
- Reverse inclusion: a standard cocharacter for `J` shows that `J` is a set
  of simple relative roots. The published `standardLeviSplitComponentStatement`
  supplies an actual split component `b : B → L_J` of the canonical standard
  Levi `Standard.leviHom i ν J` and a map `B → T` compatible with `i`.
  Re-tagging this group-scheme morphism as a morphism of commutative group
  schemes gives the data of the piece. The strict-image proposition at this
  canonical representative gives membership. No arbitrary family of
  representatives or existence hypothesis is introduced.

## Conditional reduction

`standardLeviStrictQuotientPartition_of_comparisons` proves the target from
the two exact propositions `StandardLeviStrictImageStatement` and
`ConeQuotientComparisonStatement`. The latter gives a monoid equivalence `e`
from the multiplicative form of the nonnegative integral quotient
`CocharacterCone.quotient T R` (with `R` the simple relative roots, modulo
their integral common annihilator) onto `CAplusQuotient F T R A₀ f₀`, whose
value on the class of every nonnegative integral cocharacter `ξ` is the
image of the uniformizer point of `ξ`.

By the identification above, every point of an actual piece for `J` is the
value of `e` at an integral quotient point in `CocharacterCone.strictFace i ν J`
(a standard cocharacter has nonnegative pairings with all simple roots), and
conversely `e` maps every point of that strict face into the actual piece.
Hence each piece lies in the nonnegative quotient, since values of `e` do.
For a point `x` of the nonnegative quotient, the published
`CocharacterCone.existsUnique_strictFace` gives the unique strict face
containing `e⁻¹ x`; the reverse implication gives existence of the actual
piece. If `x` lies in the piece for `K`, it equals `e` of some point of the
`K` strict face; injectivity of `e` identifies that point with `e⁻¹ x`, and
uniqueness of the integral face gives `K` equal to the chosen index.

## Final theorem

`standardLeviStrictQuotientPartition` applies the conditional reduction to
the published proofs `standardLeviStrictImage` (module
`Langlands.Geometry.Building.StandardLeviStrictUniformizerProof`) and
`coneQuotientComparison` (module
`Langlands.Geometry.Building.CocharacterUniformizerConeQuotientProof`).
The kernel axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Scope and provenance

This is an internal proof route for the derived lattice version of the strict
decomposition in David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, V.3.24, printed p.117 / PDF
p.123, with the common-uniformizer construction of V.2.5, printed p.107 /
PDF p.113, and the lattice reading of (V.3.21.1), printed p.116 / PDF p.122.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof covers both field characteristics, non-split ambient groups,
nonreduced relative root systems, empty pieces and rank zero. It proves no
freeness or finite generation and no decomposition of the full
rational-point cones in (V.3.21.1); those source assertions have the
counterexamples recorded in the Chapter V ledger.
