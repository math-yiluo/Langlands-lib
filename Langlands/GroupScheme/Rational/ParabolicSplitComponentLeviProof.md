# A parabolic split component and its Levi centralizer

The module `Langlands.GroupScheme.Rational.ParabolicSplitComponentLeviProof`
proves

```lean
Langlands.GroupScheme.parabolicSplitComponentLevi :
  Langlands.GroupScheme.ParabolicSplitComponentLeviStatement.{u}
```

It imports the published statement by Lean name. The theorem has exactly that
statement as its type, with the same universe parameter `u`.

## Statement and sources

Let `k` be any field, `G` a connected reductive group scheme over `k`, and
`j : P ⟶ G` a rational parabolic. Supply its geometric solvable radical
`r : R ⟶ P` and a maximal split torus `a : A.toGrp ⟶ R`. The theorem constructs
`m : M ⟶ P` and `aM : A.toGrp ⟶ M` such that:

- `m` is a rational Levi factor of `P`;
- `m ≫ j` represents the entire subgroup functor
  `torusCentralizer (a ≫ r ≫ j)`;
- `aM ≫ m = a ≫ r`;
- `aM` is a split component of `M`, meaning a central split subtorus maximal
  among central split subtori by the Library's factorization criterion.

The supplied radical is a hypothesis; this theorem does not construct one.
Centralizer representation is an equality on all relative test schemes, as
encoded by `SubgroupFunctor.IsRepresentedBy`.

The mathematical assertion is Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, V.3.1, printed p.110 / PDF p.116.
His definition of a split component of a possibly nonreductive group is V.2.1,
printed p.104 / PDF p.110: it is a maximal split torus in the radical. For a
reductive group it is a maximal central split torus. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
These passages were read for this proof. Renard's field is a nonarchimedean local
field; the published target and this proof work over an arbitrary field.

Borel–Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), Theorem 4.15(b),
printed p.91 / PDF p.38, gives the arbitrary-field centralizer description for
maximal split tori of the parabolic radical. That page was also read. The source
is registered as `borel-tits-1965-groupes-reductifs`, at
`/home/taskhub/central-library/Borel-Tits--Groupes reductifs--1965.pdf`.
The implemented proof below composes published Library results and does not
follow the root-order argument printed there.

## Implemented proof

The two private helper theorems are internal derived results. Their provenance
is the following composition of existing dynamic, image, centrality, and torus
extension lemmas. The first helper adapts the construction of
`IsRationalLeviSubgroup.exists_maximalTorus_radical_centralizer` in
`ParabolicRadicalTorusInitialLevi` by extending to a maximal **split** torus in
the radical.

First, `exists_maximalSplitTorus_radical_centralizer` starts with a rational Levi
`l : L ⟶ P` and a cocharacter `χ` whose dynamic centralizer in `G` is represented
by `l ≫ j`. The cocharacter factors centrally into `L` by
`torusCentralizerFactor`, using equality of the multiplicative-group torus
centralizer and the dynamic centralizer. Its dominant split-torus image `D` is a
closed central split torus of `L`. The published
`IsRationalLeviSubgroup.centralTorusRadicalFactor` embeds `D` into the supplied
solvable radical `R`.

`exists_maximalSplitTorus_extension` extends that split subtorus to a maximal
split torus `s : S.toGrp ⟶ R`. In particular, `χ` factors through `S` in `G`.
`Dynamic.torusFactor` then factors `S` into `L`. Cancellation through the closed
map `j` identifies its image in `P` with `s ≫ r`. The published lemma
`IsRationalLeviSubgroup.isCentral_of_factor_solvableRadical` makes this factor
central in `L`.

Both inclusions of the required centralizer equality are proved. Every point of
`L` centralizes `S` by that centrality, after every test-scheme refinement.
Conversely, centralizing `S` implies centralizing the cocharacter that factors
through it, so the point lies in the represented dynamic centralizer `L`. Thus
`l ≫ j` represents the whole ambient centralizer of `S`.

Second, `exists_initial_maximalSplitTorus_levi` constructs the input to the first
helper. The proved `parabolicDynamic` chooses a cocharacter for `P`. Its affine
dynamic centralizer is represented and is connected reductive by the proved
`dynamicCentralizerReductive`. The published dynamic geometric-unipotent-radical
and Levi-decomposition lemmas give a rational Levi factor of `P`, including the
scheme-level multiplication isomorphism required by `IsRationalLeviSubgroup`.
The first helper supplies an initial maximal split torus `S` of `R` with this
Levi as its ambient centralizer.

The main theorem applies `solvableMaximalSplitTorusConjugacy` to the smooth,
connected, affine solvable group `R`. It conjugates the initial `S` to the
supplied `A` over `k`, with an isomorphism of their source group schemes.
`SubgroupConjugate.exists_rationalLevi_torusCentralizer` transports the initial
Levi and the centralizer representation along that conjugacy, producing
`m : M ⟶ P` representing the ambient centralizer of `A`.

The canonical `torusCentralizerFactor` supplies `aM`. Its composition identity,
cancelled through `j`, gives `aM ≫ m = a ≫ r`. Since `a ≫ r ≫ j` is a split
subtorus of `G`, its canonical factor in the closed representative of its
centralizer is a central split subtorus of `M`.

For maximality, take a central split subtorus `b : B.toGrp ⟶ M` and a
factorization `f ≫ b = aM`. Apply `centralTorusRadicalFactor` again, now to
`b`, to obtain a closed split subtorus `bR : B.toGrp ⟶ R` satisfying
`bR ≫ r = b ≫ m`. Cancellation through the closed radical map `r` gives
`f ≫ bR = a`. The supplied maximal splitness of `a` makes `f` an isomorphism.
This is exactly the remaining maximality clause of `IsSplitComponent aM`.

## Dependencies and scope

| Direct import | Role |
| --- | --- |
| `Rational.ParabolicSplitComponentStatements` | The unchanged target proposition and its predicates. |
| `Rational.ParabolicRadicalTorusInitialLevi` | The existing whole-torus construction and its image, radical-factor, centrality, and dynamic Levi infrastructure. |
| `Rational.MaximalSplitTorusCentralizer` | Maximal split torus extension and split-subtorus centralizer factorization infrastructure. |
| `Rational.LeviTorusCentralizerConjugacy` | Transport of the Levi centralizer representation along rational subgroup conjugacy. |
| `Rational.SolvableMaximalSplitTorusConjugacyProof` | Unconditional conjugacy of maximal split tori in the supplied radical. |
| `Absolute.ParabolicDynamicProof` | A cocharacter defining the supplied rational parabolic. |
| `Dynamic.CentralizerReductiveProof` | Connected reductivity of its dynamic centralizer. |

Every module prefix in this table is `Langlands.GroupScheme.`. All structural
inputs used by the proof are published theorems. The proof uses rational
conjugacy in `R`; the stronger assertion of conjugacy by the unipotent radical
is not needed. No sibling split-component statement is assumed. This module proves
only `ParabolicSplitComponentLeviStatement`; the other statements and their
conjunction are proved in their own modules, the conjunction
`ParabolicSplitComponentStatements` as `parabolicSplitComponents` in
`Rational.ParabolicSplitComponentStatementsProof`. The statement module
`Rational.ParabolicSplitComponentStatements` and its imports do not depend on
this module.
