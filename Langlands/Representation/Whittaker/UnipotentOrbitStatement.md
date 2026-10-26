# Upper-parabolic full-unipotent orbit parametrization and ordering

Authors: Worker 197 (formal statement and documentation), Worker 330
(precise interface and consumer design).

`Langlands.Whittaker.UnipotentOrbitStatement.{uF}` is a closed, transparent
`Prop`-valued definition. It states a geometric prerequisite for the induced
Whittaker localization argument and supplies no proof.

For every prime `p`, every `F : PadicField.{uF} p`, every natural number `n`,
and every `B : GeneralLinear.BlockShape (n + 1)`, set

```text
G = GeneralLinear (n + 1) F.Carrier
P = B.parabolic F.Carrier
U = GeneralLinear.upperUnipotent (n + 1) F.Carrier
W = Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1)).
```

The proposition installs `F.canonicalTopologicalData.topology` and its
proved `generalLinearTopologicalGroup (n + 1)` certificate internally.
Thus the quotient topology is the canonical one, with no supplied topology
or topological certificate. The carrier universe `uF` is arbitrary, and
all positive ranks, including rank one, occur.

The first conjunct asserts bijectivity of the explicit map

```text
W → DoubleCoset.Quotient (P : Set G) (U : Set G)
w ↦ DoubleCoset.mk P U (GeneralLinear.permutation (n + 1) F.Carrier w.val)⁻¹.
```

The domain is the existing finite subtype of actual permutations: `w` is
strictly increasing on every source block of `B`, and `w.symm` is strictly
increasing on every target singleton block. The latter conditions are
vacuous. No chosen parametrization is an input. The right subgroup is the
full upper-unipotent group, whose diagonal entries are all one.

The second conjunct asserts the existence of `m : ℕ`,
`s : Geometric.OrderedDoubleCosets P U m`, and an equivalence `e : Fin m ≃ W`
satisfying, for every `i : Fin m`,

```text
s.representative i = GeneralLinear.permutation (n + 1) F.Carrier (e i).val.
```

The existing structure supplies a cover of `Induction.LeftQuotient P` by
pairwise disjoint actual `U`-orbits, with every initial union open. Its
`cosetOrbit P U w` is the range of `u ↦ P w⁻¹ u`. Consequently the stored
representative is the permutation matrix itself, whereas the double-coset
map uses its inverse. The equivalence and equality retain exactly the
minimal permutations needed for later stabilizer and character calculations.
No particular first index or distinguished open-orbit representative is
prescribed. Finiteness, bijectivity, an ordering, local closedness, and
comparison data are not hypotheses. There are no representation coefficients,
representations, or characters in the proposition.

## Source and derived convention

François Rodier, *Modèles de Whittaker des représentations admissibles des
groupes réductifs p-adiques quasi-déployés*, author manuscript, modified form
described by the author as 1975, Chapter V.2, Lemma 6 and Theorem 4 with its
proof, PDF pages 36–42. These pages were read and their scanned formulas
visually inspected. Theorem 4 starts on PDF page 36, Lemma 6 is on page 37,
and the proof on pages 38–42 studies equivariant distributions on `U w P`.
Page 41 uses a finite disjoint decomposition into these double cosets and an
order in which each successive orbit is open in the remaining union.
Lemma 6 supplies a character criterion identifying the distinguished orbit;
that criterion and the distribution arguments are outside this statement.

The source is registered as `rodier-whittaker-author-manuscript`. Its retained
file is
`/home/taskhub/central-library/Rodier--Modeles de Whittaker des representations admissibles des groupes reductifs p-adiques quasi-deployes--1975/Rodier--Modeles de Whittaker (author manuscript).pdf`,
with verified SHA-256
`8c110b6b626108ec67421f288baa4b761a8073df2c68db6be8360b654f569812`.
The adjacent source README identifies this as the 46-page author manuscript,
not the six-page 1973 proceedings paper, and records uncertainty about the
exact scan revision and possible pagination gaps elsewhere. No applicable
published erratum was present at the time of this reading.

This precise GL proposition is a derived geometric interface, not a literal
transcription of Rodier's normalized distribution theorem. Inversion sends
his `U w P` double coset to `P w⁻¹ U`. On the left quotient `P \ G`, these
are orbits for right multiplication by `U`; using the inverse right action
to express a left group action gives the same orbit sets. This matches the
existing `WeylDefinitions.parabolicDoubleCoset` and
`ClosedSubgroupDefinitions.cosetOrbit` inverse-representative conventions.
The finite subtype and its within-block conditions come from those existing
GL Weyl definitions. The exact matrix representative requirement is added
for the downstream concrete calculations.

## Existing results and remaining proof obligations

The imported Library pairs `Geometric.WeylDefinitions`, `GL.SingletonBlocks`,
`GL.UpperUnipotent`, `GL.Padic`, and `Geometric.ClosedSubgroupDefinitions` are
reused unchanged. They supply the actual permutations, block shapes,
subgroups, canonical topology and ordered orbit structure. No new substantial
definition is introduced.

A future proof may reuse
`Langlands.GeneralLinear.fieldUpperBruhatFactorizationTheorem` from
`Langlands.Group.GL.UpperBruhatProof` and
`Langlands.Geometric.padicParabolicBruhat` from
`Langlands.Representation.Geometric.PadicParabolicBruhatProof`.
For the singleton parabolic, an upper triangular right factor must be
factored as a diagonal torus element times an upper-unipotent element.
Conjugating that torus element by a permutation matrix gives another diagonal
element, which lies in `P` and can be absorbed on the left. These algebraic
factorizations, subgroup memberships and quotient equalities require proofs.
Equality of full-`U` double cosets can then be compared with singleton-parabolic
double cosets to use the existing minimal-representative uniqueness. Ordinary
parabolic Bruhat alone is not the full-`U` bijection asserted here.

The bijection would make the actual double-coset quotient finite.
`Langlands.Geometric.closedSubgroupOrbitOrdering` from
`Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering` then offers
a general finite-orbit ordering once its closedness and topological hypotheses
have been discharged for these groups. Its arbitrary representatives must
also be matched bijectively to `W` and replaced by the exact permutation
matrices, proving equality of orbit sets so that coverage, disjointness and
open initial unions are retained. All these reductions remain separate proof
obligations. The existing closed-subgroup Mackey filtration theorem concerns
the subsequent representation-theoretic step and is not asserted or proved
by this module.
