# Exact exponent shifts for actual unramified normalized Jacquet modules

Author: Worker 135. This module specializes the published natural Jacquet
twist comparison to arbitrary unramified characters and proves the exact
shift of normalized Jacquet exponents. It also decomposes the exponents of
actual full geometric-lemma pieces of a twisted source. All local-field and
representation carrier universes `u` and `v` remain independent.

## Natural comparison and exponent equality

The ambient affine group scheme `G` is over a nonarchimedean local field,
whose topology is Hausdorff. Its rational points carry the canonical topology,
assumed locally compact and a nonarchimedean group. The parabolic, rational
Levi, geometric radical and multiplication isomorphism are the specified
actual maps `p`, `l`, and `r` with their published proofs.

`leviJacquetUnramifiedTwistIso` is a natural isomorphism between twisting
before `leviJacquetFunctor` and twisting afterwards by the original
unramified character restricted along `l >> p`. It uses
`leviJacquetTwistIso` from `RepresentedGeometricLemmaSourceJacquet` and
`pointImage_radical_le_ker_unramifiedSmoothCharacter` from
`UnramifiedTwistRadicals`. In particular, radical triviality is proved, not
an extra premise. No quotient comparison is reconstructed here.

For a specified split component `a : A -> M`, let `theta` be the original
character restricted along `a >> l >> p`. The theorem
`isNormalizedJacquetExponent_unramifiedTwist_iff` states

```
chi is a normalized Jacquet exponent of pi twisted by psi
iff chi * theta inverse is a normalized Jacquet exponent of pi.
```

It restricts the actual representation equivalence underlying the natural
comparison to `A(F)`, then applies the existing exact generalized-eigencharacter
twist law. It uses the published equivalence between normalized Jacquet
exponents and generalized eigencharacters on the transported Jacquet module.
There is no admissibility, finite length, irreducibility, temperedness or
semisimplicity premise in this equivalence.

`exists_normalizedJacquetExponent_untwist` packages the conclusion as
`chi = chi0 * theta`, where `chi0` is an actual untwisted normalized Jacquet
exponent. The real-part equality is the sum of their published normalized
real parts, by `normalizedRealPart_mul` and `normalizedRealPart_inv`.

## Actual full geometric-lemma pieces

For arbitrary valid `GeometricLemmaIntersectionDatum D`, a target Levi split
component `a`, a split component `a'` of `D.L'`, and a factor `f : A -> A'`
satisfying the published target-side factorization,
`exists_untwisted_sourceJacquetExponent_of_twisted_piece` takes a generalized
eigencharacter `chi` on the actual full piece at `sigma` twisted by an
unramified character `psi` of the source Levi. It obtains an actual normalized
Jacquet exponent `theta` of untwisted `sigma` along `D.p'`, with split
component `a' >> D.phi.hom`, such that

```
chi = restriction of theta along f
    * restriction of psi along f >> a' >> D.phi.hom >> D.l' >> D.p'.
```

It also proves the corresponding additive normalized real-part identity on
`A`. Every map is the original group-scheme morphism from `D` or the supplied
factor `f`; no Weyl representative or replacement piece is introduced.

This theorem explicitly retains admissibility of the normalized Jacquet
module of the twisted source along `D.p'`. That is the premise of the
published `exists_isNormalizedJacquetExponent_of_piece`, which transfers a
full-piece exponent to a source Jacquet exponent. Applying the newly proved
untwisting theorem gives `theta`. The original factorization on characters
then gives the displayed formula, and real-part additivity gives the last
conjunct. This result does not prove Jacquet admissibility.

## Source, derivation and remaining obligations

David Renard, *Representations des groupes reductifs p-adiques*, French version
of 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 135 read VII.4.1's Lemma and proof, printed pp.241--242 / PDF
pp.247--248. The proof's initial decomposition of the twisted Jacquet
exponents and subsequent separation of their two real parts motivate this
derived general formulation. The implemented proof composes the existing
actual Jacquet twist comparison, unramified radical triviality,
generalized-eigencharacter equivalence, full-piece exponent transfer and
real-part laws. It does not use Langlands classification or opposite regularity.

For Task 5282, the tempered untwisted contribution still needs its cone
comparison at the relevant pieces. The twist factor's normalized real part
must be identified with the Weyl translate of the inducing parameter, and
nonidentity parabolic double cosets must be related to Weyl classes outside
the actual Levi subgroup. The new strict Weyl-displacement lemmas then apply.
The geometric lemma, VII.3.3 criterion and opposite identity-support result
remain independently owned proof inputs. None is asserted by this pair.
