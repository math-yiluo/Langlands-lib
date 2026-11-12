# Completeness of Whittaker functions (proof)

This module proves `Langlands.Whittaker.WhittakerCompletenessStatement.{uF, uV}` for arbitrary
universes `uF` and `uV`, as the theorem
`Langlands.Whittaker.CompletenessProof.whittakerCompleteness`. It adds no hypotheses. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

Fix a prime `p`, `F : PadicField p` with its canonical structures, a unitary additive
character `ψ` and an index `n`. Let `H` be a function on `GL_(n+1)(F)` with
`H(u g) = ψ_N(u)⁻¹ H(g)` (an element of `InverseWhittakerFunctions ψ n`) such that:
- `H` is right invariant under an open subgroup;
- `H` vanishes outside `N_(n+1) C` for a compact set `C`;
- `∫ W H = 0` for the canonical quotient measure `unipotentQuotientHaar` on
  `N_(n+1) \ GL_(n+1)(F)`, for every vector `W` of the coefficient model of every Whittaker
  functional of every generic representation on a carrier in `Type uV`.

Then `H(g) = 0` for every `g` (Jacquet and Shalika 1985, Lemma (3.2)).

## Proof

The proof applies the published theorem `RankinSelberg.supercuspidalProductCompleteness`
(Henniart 1993, Lemme 2.1) to the character `ψ⁻¹ = ψ.scale (-1)`. The function `H` is read as
the `ψ⁻¹`-Whittaker function `H' = InducedTailIntermediate.inverseAsScaledStandard ψ H`, which
has the same underlying function. Henniart's lemma needs `H'` to be orthogonal to every
normalized product of irreducible supercuspidal representations. The hypothesis of the target
gives orthogonality only to the generic ones, so the main work is the passage from the
irreducible products to all products. Orthogonality is the predicate
`CompletenessOrthogonality.Orthogonal`, which is invariant under equivalence
(`orthogonal_iff_of_equiv`).

### Whittaker type of the two parts of a cut (`isOfWhittakerType_partProduct`)

A cut `C : CompletenessCut.Cut k` splits the blocks `τ_1, …, τ_k` into a head and a tail.
The normalized product of each part (`C.partProduct`) is of Whittaker type, by
`normalizedProductWhittakerType`. Each block is of Whittaker type by
`isOfWhittakerType_of_supercuspidalKirillov` applied to the published `supercuspidalKirillov`.

### The cut equivalence (`orthogonal_cutTwist_iff`)

Twist the tail blocks of the cut by `|det|^u`, `u` real (`C.cutTwist`). Let `ρ_u` be the
deformed two-block representation of JPSS 1983, Section (4.5), of the tail and head products
(`twoBlockDeformedInduced`). Orthogonality to the normalized product of the twisted blocks is
equivalent to orthogonality to `ρ_u`. The proof combines the published equivalence
`C.cutEquiv` with `orthogonal_iff_of_equiv`.

### The induction (`orthogonal_of_irreducible`)

Fix a measure `μ` on the quotient, finite on compact sets, and a compact Whittaker test
function `H` (`IsCompactWhittakerTestFunction`). Assume (`hbase`) that `H` is orthogonal to every
irreducible normalized product of smooth irreducible supercuspidal blocks with a given
shape. Then `H` is orthogonal to every normalized product of that shape.

Each block has a cuspidal datum (`blockDatum`). The proof is a strong induction on
`linkedCount`, the number of ordered pairs `(a, b)` of blocks with
`ρ_a = ν ρ_b` (`ν = |det|`).

- No linked pair. The product is irreducible
  (`isIrreducible_canonicalNormalizedProductInduced_of_unlinked`), and `hbase` applies.
- Some linked pair. `exists_crossing_of_linkedCount_ne_zero` gives an index `j` and a linked
  pair `(a, b)` with exactly one of `a, b` after `j`. Then `j + 1 < k`. Cut after block `j`,
  so `C.c = j + 1`. The predicate `S i ↔ C.c ≤ i` marks the tail, and the linked pair crosses
  the cut.
  1. For real `u ≠ 0` near `0`, twisting the tail by `ν^u` gives strictly fewer linked pairs
     (`eventually_linkedCount_twistOn_lt`). The twisted blocks `twistBlocks c τ`, with
     `c i = u` on the tail and `0` on the head, are smooth, irreducible and supercuspidal
     (`isSmooth_twistBlocks`, `isIrreducible_twistBlocks`, `isSupercuspidal_twistBlocks`).
     Their cuspidal data are, by definition, the twisted data `twistOn S u (blockDatum τ …)`
     (as in `blockDatum_twistBlocks_ite`). By the induction hypothesis `H` is orthogonal
     to their normalized product. That product is the cut product `C.cutTwist m F τ u`, by
     definition. By `orthogonal_cutTwist_iff`, `H` is orthogonal to `ρ_u`.
  2. Both parts are of Whittaker type, so the deformation step
     `orthogonal_twoBlockDeformedInduced_zero` gives orthogonality to `ρ_0`. Here each
     Whittaker function of `ρ_0` is a limit of Whittaker functions of `ρ_u` with one common
     right stabilizer.
  3. By `orthogonal_cutTwist_iff` at `u = 0` and `cutTwist_zero`, `H` is orthogonal to the
     untwisted product.

### Assembly (`orthogonal_canonicalNormalizedProductInduced`, `whittakerCompleteness`)

Under the hypotheses of the target, with an arbitrary measure `μ` finite on compacts in place
of the canonical one, `H'` is orthogonal to every normalized product of smooth irreducible
supercuspidal blocks (`orthogonal_canonicalNormalizedProductInduced`).
- `H'` is a compact Whittaker test function for `ψ⁻¹`
  (`isCompactWhittakerTestFunction_inverseAsScaledStandard`).
- The base case of the induction holds: an irreducible product is generic
  (`isGeneric_canonicalNormalizedProductInduced`), and the hypothesis on `H` gives
  orthogonality of `H'` to every generic representation for `ψ⁻¹`
  (`orthogonal_scale_neg_one_of_isGeneric`). That lemma accepts generic representations in any
  universe, so the target's restriction to carriers in `Type uV` is enough.

The main theorem fixes the Borel σ-algebras of the target and takes
`μ = unipotentQuotientHaar F n`. This measure is regular, hence finite on compacts, and
compatible with `generalLinearHaar` and `unipotentHaar` (`unipotentQuotientHaar_isCompatible`).
- Rewrite orthogonality in the coefficient-model form of Henniart's lemma
  (`orthogonal_iff_forall_coefficientModel`).
- Apply `supercuspidalProductCompleteness.{uF, uV}` at `ψ.scale (-1)`, which gives `H' = 0`.
- Since `H'` has the underlying function of `H`, `H(g) = 0` for every `g`.

## Provenance

The target is Jacquet and Shalika 1985, *A lemma on highly ramified ε-factors*, Lemma (3.2)
(printed page 325), whose proof is that of Jacquet, Piatetski-Shapiro and Shalika 1981, Lemme
(3.5). The sources argue spectrally. The route implemented here instead reduces to Henniart's
Lemme 2.1, already published for normalized products of supercuspidals. It then passes from
irreducible products to all products by the deformation of JPSS 1983, Section (4.5).

This module adds only internal lemmas, none from the literature. Their meaning is given above.
The supporting modules `CompletenessOrthogonality`, `CompletenessCut`,
`CompletenessTwistFiniteness`, `CompletenessUnlinkedBase` and `CompletenessPairing` are in the
Library.
