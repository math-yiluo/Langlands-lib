# The unitary Jacquet part at the identity parabolic

This internal derived unit supplies the nonempty starting case in the first
proof paragraph of Renard, *Représentations des groupes réductifs p-adiques*
(9 July 2026), VII.2.6, printed p.231 / PDF p.237. Renard chooses a parabolic
minimal with nonzero unitary Jacquet part and observes that the whole group
satisfies this property. The Lean proves that observation for the published
normalized-exponent temperedness predicate and the actual normalized Jacquet
functor.

The field has universe `u` and the smooth complex representation has independent
carrier universe `v`. The hypotheses retain the nonarchimedean local field,
canonical rational-point topology, local compactness, nonarchimedean group
structure and connected reductivity. The identity parabolic and identity Levi
are equipped with any specified witnesses and any matching represented geometric
unipotent radical and multiplication isomorphism. The split component is an
actual map into the whole group. No scalar central character, finite length,
irreducibility, extra presentation coverage or Jacquet-admissibility hypothesis
is used.

The full-group normalized exponent theorem makes every nonzero Jacquet weight
have zero normalized real part. Therefore every Jacquet weight space lies in
the unitary part and the nonunitary part is zero. To prove that the unitary
part is the whole Jacquet module, the implementation uses admissibility of the
source, which is part of temperedness. The published central-weight spanning
theorem applies to the original source. The ordinary coinvariant projection
intertwines the split-component action, since normalization is trivial on
ambient central points. This projection is surjective and maps each source
weight into the corresponding normalized Jacquet weight. Mapping the spanning
supremum through it proves that the unitary part equals the top
subrepresentation. This route needs no admissibility theorem for the Jacquet
module.

The definition `temperedIdentityUnitaryJacquetEquiv` restricts the ordinary
coinvariant projection to the actual unitary submodule. The identity radical
has trivial actual point image, so the endpoint coinvariant equivalence proves
injectivity; ordinary coinvariant surjectivity proves surjectivity. The result
is a linear equivalence from the original carrier to the actual unitary
identity Jacquet part, with an application lemma identifying its underlying
vector with the literal coinvariant class. No identification of the two
acting groups is asserted by this linear equivalence. A nontrivial source
therefore gives a nontrivial actual unitary subrepresentation. Finally the
published split-component existence theorem chooses an actual split component,
and the canonical kernel-of-unit radical gives an explicit nonempty instance
of the family used to start the minimality argument.

These are supporting results for VII.2.6. They do not construct a minimal
parabolic, prove Jacquet transitivity or quotient temperedness, or establish
square-integrability, uniqueness or unitarizability.
