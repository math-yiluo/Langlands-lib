# The center on the normalized Jacquet modules of the minimal principal series

`Langlands.HarishChandraSchwartz.rationalMinimalInducedJacquetUnipotent` proves
`RationalMinimalInducedJacquetUnipotentStatement.{u}`. For each standard parabolic
`P_J`, the proof obtains one power of `π_P(z) − 1` that vanishes for every
central point `z` of the actual Levi `M_J(F)`.

## Source

Waldspurger computes the graded pieces in I.3, printed pp. 243–244, and uses the
uniform power bound on the split component in the proof of Lemme II.1.1, printed
p. 251. The proof here uses that computation to obtain the whole-center form in
the Library statement. The registered source is `waldspurger-2003-plancherel`.
[Waldspurger 2003](https://doi.org/10.1017/S1474748003000082)

## Lean proof

`ParabolicDatum.standard` supplies the represented parabolics for the empty
simple-root subset and for `J`. The range of the minimal Levi is the centralizer
of the original maximal split torus, by
`standardLevi_empty_eq_torusCentralizer_of_generic`. The published
`representedGeometricLemma` supplies the finite double-coset enumeration,
intersection data, and a filtration whose graded pieces are identified
up to permutation. The proof evaluates this filtration on the trivial smooth
character of the represented minimal Levi.

For each piece, the common maximal split torus of its intersection datum maps
into the minimal Levi, so its image commutes with the original torus and its
inclusion factors through that torus. The conjugate target parabolic is
represented by the dynamic parabolic of a cocharacter of the common torus,
which lies in its Levi. The cocharacter therefore factors through the original
torus. Its dynamic parabolic contains the original torus centralizer, which
makes the source parabolic intersection the full minimal Levi.
`fullLeviJacquetEquiv_representation` identifies the normalized Jacquet action
for this full intersection with restriction of the original action. The
trivial action survives the pullbacks along the intersection Levi isomorphism
and the identification with the literal inducing Levi image.

A central point of the target Levi commutes with the target-side common
torus on rational points. Over the given infinite field,
`normalizerPointsInfiniteField` identifies this point centralizer with the
rational points of the torus centralizer. The latter lies in the centralizer
of the common-torus cocharacter defining the conjugate source Levi. The
intersection identity for the target-piece Levi then places the point in
that Levi's rational image. `normalizedInductionCentralCharacter_acts`
shows that its action on the induced piece is trivial. The positive half
modulus contributes one because the point is central in the ambient target
Levi and thus conjugates the piece's radical trivially.

On the finite filtration, `ρ(z) − 1` lowers every step by one using the
graded-piece isomorphisms. Its power at the filtration length takes the
top step into the zero step. The length is the number of rational double
cosets and is chosen before the central point.

The comparison in `RationalMinimalInducedJacquetBridge` specializes the
represented composite to the canonical standard parabolics for `∅` and `J`
and carries the same bound to `rationalMinimalInducedJacquet`. The target uses
the literal standard subgroups, normalized induction of the trivial minimal
Levi character, and the inverse half Haar modulus on the standard radical.
