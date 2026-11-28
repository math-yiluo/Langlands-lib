# Separation of the orbit from the compact-level complement over a p-adic field

Over a `p`-adic field `E` with topological data `T`, let `σ` be an
automorphism of `E` over `F`, with the supplied `F`-module topology. Let
`n > 0` and write `θ = entrywiseAut σ n`. The second theorem also assumes
`σ ^ d = 1` for some `d > 0`.

- `properInduced_mem_selection_or_complement`: let `s` be a multiset of
  cuspidal data and `Ξ` an irreducible admissible representation, on a
  carrier in universe `z`, of a standard Levi `B.Levi E`, with a Levi
  σ-intertwiner. Its unnormalized induced twisted trace lies in one of
  two spans: the span of the irreducible twisted traces selected by
  `supportTwistSelection T n s`, or the span of the unselected ones. The
  proof has three steps.
  1. Lift `Ξ` to universe `max v z` and untwist the half modulus.
     `CuspidalSupport.padicLeviAdmissibleFactorization` writes the result
     as a block tensor of irreducible blocks `Af`. The induced
     representation is then equivalent to the normalized product of `Af`,
     which has finite length (`irreducibleProductFiniteLength`).
  2. All irreducible subquotients of that product have one supercuspidal
     support `s'` (`exists_supercuspidalSupport_of_normalizedProduct`).
     By `supportTwistSelection_iff`, either all of them are selected or
     none is, according as some unramified twist of `s'` is `s`.
  3. Dévissage over a finite-length representation
     (`twistedDistribution_mem_of_finiteLength`) puts the induced trace in
     the corresponding span. It uses equivalent realizations of the
     subquotients on carriers in universe `z`
     (`exists_irreducible_smoothRep_equiv_of_separable`).
- `exists_compact_disjoint_twistedOrbitSpan_complement_padic`: let `τ`
  satisfy `IsSigmaDiscreteSeries σ n τ`, `n > 0`, and let `μ` be a Haar
  measure. There is a compact open subgroup `J` such that
  `twistedOrbitSpan μ θ τ` is disjoint from
  `twistedPseudoCoefficientComplementSpan σ μ τ J`. The proof has three
  steps.
  1. Choose the supercuspidal support `s` of `τ`
     (`glSupercuspidalEmbedding`). Select the irreducibles with
     `supportTwistSelection T n s`. The selection is
     equivalence-invariant, contains the σ-invariant unramified orbit of
     `τ` (`supportTwistSelection_of_isUnramifiedTwistOf`), and has fixed
     vectors at one compact level `J`
     (`exists_compact_fixed_of_supportTwistSelection`).
  2. Proper inductions split along the selection by the previous theorem.
  3. `disjoint_twistedOrbitSpan_complement_of_support` combines these
     facts with the separation from the other essentially tempered and
     proper-induction spans
     (`disjoint_twistedOrbitSpan_otherTempered_sup_properInduced`).

In Henniart–Lemaire (2011), II.5.13, pp. 113–114, the functional built
on the orbit is zero on the essentially tempered classes outside the
orbit. It is extended by zero to the induced part by II.5.11, Lemme 2.
It satisfies condition (i) of the twisted Paley–Wiener theorem (II.5.7,
p. 105) because all unramified twists of the given representation have
the same Bernstein component `j(Π)`, an inertial class of cuspidal pairs.
The selection here is finer. It keeps the representations whose
supercuspidal support becomes that of `τ` after twisting all cuspidal
data by one common unramified character.

The level `J` is not taken from the literature. It is chosen by uniform
visibility (`exists_compact_fixed_of_supportTwistSelection`). The
selected representations are σ-invariant unramified twists of irreducible
subquotients of finitely many supercuspidal products
(`exists_finite_cuspidalProducts_covering`). For those,
`exists_compact_open_fixed_constituentTwists` gives one compact open
subgroup at which all of them have nonzero fixed vectors. The
`J`-invisible span is then part of the complementary span. Its
literature counterpart is condition (i)′ of II.5.7, Remarque (1), p. 105:
a vanishing condition on a functional at the strongly irreducible
σ-representations without nonzero `J`-fixed vectors, for some compact
open `J`. The second theorem above is the disjointness of spans of
twisted distributions at the chosen level.
