# Opposite factor pairs over algebraically closed fields

Module `Langlands.GroupScheme.Rational.AlgClosedOppositeFactorPairsStatement`.

## Statement

`Langlands.GroupScheme.AlgClosedOppositeFactorPairsStatement` is an unproved
proposition at arbitrary universe `u`. It quantifies over

- an algebraically closed field `k : Type u` (`[Field k] [IsAlgClosed k]`);
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`;
- a commutative group scheme `T` over `Spec k` and an actual maximal split torus
  `i : T.toGrp ⟶ G` (`hi : IsMaximalSplitTorus i`).

With the affineness instance `hG.isAffineHom` and the monomorphism instance
`hi.isSplitSubtorus.mono`, it asserts the Library predicate
`RelativeRoot.HasOppositeFactorPairs i`. Spelled out: for every relative root
`a ∈ relativeRoots i` and every rational point `u ≠ 1` of the actual root group
`RelativeRoot.subgroup i a`, there is a pair `(u′, u′′)` of rational points of the
actual root group `RelativeRoot.subgroup i (-a)` such that `u′ * u * u′′` lies in
`normalizerPoints i`. The pair condition is the Library predicate
`RelativeRoot.IsOppositeFactorPair i a u (u′, u′′)`.

Only existence is asserted. The statement makes no claim that the pair is unique, that
`u′` or `u′′` is nontrivial, that `u′ * u * u′′` acts as the reflection in `a`, or that
`u′ = u′′`. The root groups, rational points, relative roots and normalizer are the
existing Library constructions. There is no chosen model of a root group, no
parametrization by the additive group and no `SL₂` in the hypotheses or conclusion.
The implication is quantified over nonidentity root points; it does not itself assert
that such points exist.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 2.11.17,
printed p.136 (PDF p.167), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. For a connected quasi-reductive group
`G` over a field `k`, a maximal `k`-split torus `S`, a root `a ∈ Φ(S, G)` and
`u ∈ U_a(k) − {1}`, it gives unique `u′, u′′ ∈ U_{-a}(k)` such that
`m(u) = u′ u u′′` normalizes `S`, together with further properties.

The cited original is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition C.2.24(i), printed p.620 (PDF p.646), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. It is stated for smooth connected affine
groups whose unipotent-radical weights are not integral multiples of roots. That
hypothesis is automatic for connected reductive groups, whose unipotent radical is
trivial.

This file states the **existence** part of these results, specialized to

- connected reductive groups (a special case of connected quasi-reductive groups);
- algebraically closed fields, where every maximal torus is split, and the maximal split
  torus is a maximal torus.

The Library's `RootRankOneFactorizationStatement` states the full arbitrary-field
proposition (uniqueness, nontriviality, the reflection, and the nonmultipliable-root
clauses). The present statement is a weaker specialization. It is stated separately
because the reduction of `SteinbergBigCellStatement` to independent structural inputs
(module `Reductive.SteinbergBigCellIndependentInputs`) needs only this existence over
algebraically closed fields, and it needs a proof that is independent of the
dynamic-Borel inputs. The Library's proof of `RootRankOneFactorizationStatement`
(module `Rational.RootRankOneFactorizationProof`) is not independent of those inputs.

## Use

The helper module `Rational.OppositePairBruhatCovering` takes `RelativeRoot.HasOppositeFactorPairs i`
as its only rank-one hypothesis. From it the module derives the Bruhat covering
`BorelTorusBruhatCovering` for the dynamic parabolic of a generic cocharacter over a
separably closed field. A proof of this statement therefore supplies that covering for
every maximal split torus of a connected reductive group over an algebraically closed
field.
