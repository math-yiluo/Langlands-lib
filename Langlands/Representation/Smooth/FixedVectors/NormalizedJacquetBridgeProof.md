# Fixed-vector detection for the actual normalized Jacquet functor

Worker 189. This derived proof implements
`Langlands.NormalizedJacquetFixedVectorBridgeStatement` with independent group
and carrier universes. It uses the actual Haar-normalized functor throughout.

The proof first shows that the open-kernel positive Haar character is trivial on
the compact intersection of `K` with the closed subgroup `M`. The published
inverse-half character identity then shows that the normalizing character is
trivial there. No rational-character factorization is assumed.

Generation by fixed vectors transports through an equivariant equivalence by
pulling back an invariant submodule containing the target fixed space. Apply
this to the published trivial-character localization equivalence and the
published unnormalized Jacquet generation theorem. Untwisting an invariant
submodule and identifying fixed spaces on the character kernel proves
generation for the actual normalized Jacquet module.

For actual subquotients, unpack the supplied presentation into an injective map
from a smooth object to `A` and a surjective map from that object to `D`.
The normalized functor's maps are the underlying localization maps. Naturality
of the trivial-character comparison identifies these with the old coinvariant
maps. Finite compact containment in `N` supplies injectivity, and coinvariant
right exactness supplies surjectivity. The resulting actual maps give a
subquotient presentation for the normalized Jacquet objects.

Compact-open fixed-vector exactness transfers finite dimension of `A^K` to
`D^K`: the fixed space of the intermediate object injects into `A^K` and
surjects onto `D^K`. A nonzero fixed vector in the normalized Jacquet module of
`D` is fixed in the unnormalized localization because the character is trivial
on the intersection. The comparison equivalence sends it to a nonzero fixed
vector in the old Jacquet quotient. The weak Jacquet lemma for the supplied
Iwahori contraction lifts it to a nonzero vector in `D^K`.

The accompanying derived theorem
`Langlands.normalizedJacquetSubquotientFixedVectorDetection` applies the
published finite compact-restriction detection theorem directly to the
normalized ambient Jacquet object. Its supplied actual subquotient `E`
keeps its normalized action. Transitivity makes `E` a subquotient of that
ambient object; the bridge supplies generation there. The finite nonempty
spanning family of compact irreducible representations on a normal
subgroup `H` therefore gives a nonzero intersection-fixed vector in `E`.
Compact-open exactness lifts its nonvanishing to the normalized Jacquet
object of `D`, and the bridge then lifts it to `D^K`. This theorem keeps
independent group, carrier and finite-family index universes. It assumes
the finite compact-restriction family and does not construct one.

This internal bridge implements the Jacquet generation and lifting step of
Renard VI.6.3, printed pp.178–179 / PDF184–185, French edition dated 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It supplies no rational-point structural realizations, finite compact
restriction family, existence of a cuspidal Jacquet constituent, or final
Howe finite-length conclusion.
