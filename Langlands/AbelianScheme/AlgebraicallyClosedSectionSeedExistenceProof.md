# Finite section seeds at the unit over an algebraically closed field (proof)

This module proves `Langlands.GroupScheme.AlgebraicallyClosedSectionSeedExistenceStatement`
(module `Langlands.AbelianScheme.AlgebraicallyClosedSectionSeedExistenceStatement`) as the
theorem `Langlands.GroupScheme.algebraicallyClosedSectionSeedExistence`, with no hypothesis.

## Statement proved

For every universe `u`, every algebraically closed field `K : Type u` and every commutative
group object `G` in schemes over `Spec K` whose structure morphism `G.X.hom` is smooth,
proper and geometrically connected, there are `n : ℕ`, line bundles
`L : Fin n → LineBundle G.X.left` and global sections `s i` of `L i` forming a finite
point-tangent section seed at the unit `(1 : Over.mk (𝟙 (Spec K)) ⟶ G.X).left`, in the sense
of the published `Langlands.AlgebraicGeometry.Picard.IsFinitePointTangentSectionSeed`. The
size `n` may be zero.

## Proof

The module has two theorems.

`algebraicallyClosedSectionSeedExistence_of_primeGermDivisorSection` derives the statement
from the proposition `Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement`,
taken as a hypothesis `hS1`:

1. `G.X.left` is Noetherian: it is compact because the proper structure morphism is
   quasi-compact and `Spec K` is compact (`QuasiCompact.compactSpace_of_compactSpace`), and
   locally Noetherian because it is locally of finite type over a field
   (`LocallyOfFiniteType.isLocallyNoetherian`).
2. The unit `z` is a rational point: `z ≫ G.X.hom = 𝟙` is the commutativity of the unit
   morphism in the category over `Spec K` (`Over.w`).
3. `separation_of_primeGermDivisorSection hS1 K G z hz` (module
   `Langlands.AlgebraicGeometry.Picard.PrimeGermPointwiseSeparation`) gives the two
   pointwise separation hypotheses: every rational point `x ≠ z` and every nonzero tangent
   vector at `z` is detected by a global line-bundle section that vanishes along `z` and
   does not vanish along some rational point.
4. `finiteSeedOfSeparation` (module
   `Langlands.AlgebraicGeometry.Picard.FiniteSeedOfSeparationProof`, a proof of
   `FiniteSeedOfSeparationStatement`) turns these hypotheses on the Noetherian scheme
   `G.X.left` into a finite seed.

`algebraicallyClosedSectionSeedExistence` applies this theorem to
`primeGermDivisorSection : PrimeGermDivisorSectionStatement` (module
`Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionProof`), so the final theorem has
no hypothesis.

## Supporting modules

The proof consists of the following modules, all part of this contribution, in dependency
order (each has its own Markdown file describing it):

* `Langlands.AlgebraicGeometry.Modules.FrameVanishingCriterionStatement` and
  `...FrameVanishingCriterionProof`: a section with coefficient `a` in a local frame
  vanishes along a morphism into the frame's open exactly when `a` pulls back to zero
  (`frameVanishingCriterion`).
* `Langlands.AlgebraicGeometry.Picard.AssociatedEquationGluing`: nonzero local equations on
  an open cover of an integral scheme whose germs are associated on overlaps glue to a line
  bundle with a global section, with the expected generation open and vanishing criterion
  (`exists_lineBundle_of_associated_equations`; uses cocycle gluing and the frame
  criterion).
* `Langlands.AlgebraicGeometry.Picard.PrincipalLocalization` and
  `...PrimeDivisorEquations`: local equations of the closure of the coheight-one point of a
  prime germ, on a locally Noetherian integral scheme with factorial stalks.
* `Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement` and
  `...PrimeGermDivisorSectionProof`: a prime germ gives a line-bundle section cutting out
  its prime divisor (`primeGermDivisorSection`).
* `Langlands.AlgebraicGeometry.Picard.PrimeGermPointwiseSeparation`: point and tangent
  separation on a smooth proper geometrically connected commutative group scheme over an
  algebraically closed field, using the published local factoriality theorem
  `Langlands.AlgebraicGeometry.smoothAlgClosedFactorialStalks`.
* `Langlands.AlgebraicGeometry.Picard.FiniteSeedOfSeparationStatement` and
  `...FiniteSeedOfSeparationProof`: Noetherian finiteness (`finiteSeedOfSeparation`).

The three statement modules carry, unchanged, the statement texts of the statement tasks
75c63d90-3732-4ddc-8eee-8d3c9f495992, ccde8b6e-eab2-4800-89b1-cb3b09bfdaee and
54d78782-5b23-49ac-b02a-c9b4bae3a2ab, published from this proof task as its planned split;
those tasks received no executor, so the statements are submitted here with their proofs.

## Provenance

This is the first step of Milne's proof of Theorem 7.1 (J. S. Milne, *Abelian Varieties*,
corrected author version January 2, 2022, p. 11), in section form: the prime divisors `Zᵢ`
through `0` and their line bundles `L(Zᵢ)` are replaced by the line bundles and sections of
`PrimeGermDivisorSectionStatement`, and the finite choice of `{Zᵢ}` with properties (a) and
(b) is `finiteSeedOfSeparation`. No projectivity, ample line bundle or separating line
bundle result is used. The proof makes no characteristic or dimension assumption; in
dimension zero the produced seed is necessarily empty (see the discussion of `n = 0` in the
published `FiniteSectionSeed.md`).
