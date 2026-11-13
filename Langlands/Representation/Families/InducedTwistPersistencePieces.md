# Irreducible subquotients of `r_{R'} i_R` of a supercuspidal representation

Author: Worker 5120.

This module classifies the irreducible subquotients of `X = r_{R'}(i_R(τ))` for a
supercuspidal irreducible `τ`. Here `R` and `R'` are actual parabolics of `G` with the
same embedded Levi `L`. All declarations are in `Langlands.InducedTwistPersistence`.

## Results

- `pullbackConjEquiv`: suppose `e' x = e(m x m⁻¹)` for automorphisms `e`, `e'` of a
  topological group `Γ`. Then the pullbacks of `τ` along `e` and `e'` are equivalent,
  through the action of `e(m⁻¹)`.
- `hasFiniteLength_and_classify_of_filtration`: take a finite filtration of a smooth
  representation whose graded pieces are equivalent to given irreducible representations
  `P i`. Then the representation has finite length, and each of its irreducible
  subquotients is equivalent to some `P i`. The proof combines
  `hasFiniteLength_of_hasSimpleFactors` and the published `simpleSubquotientFactor`
  (Jordan–Hölder).
- `pieces_of_supercuspidal`: let `τ` be supercuspidal and irreducible, in the form "every
  proper actual Jacquet module vanishes", and let `lR' ≫ r' = lR ≫ r`. Then `X` has finite
  length, `X` is supercuspidal, and every irreducible subquotient of `X` is equivalent to
  a pullback of `τ` along the point map `e` of an automorphism `φ` of `L`. This `φ`
  satisfies `φ ≫ lR ≫ r = lR ≫ r ≫ Int(z)` for some `z ∈ G(k)`.
- `pieces_of_supercuspidal_normalizer`: let finitely many representatives `g j` with
  automorphisms `φ j` be given, such that every `w ∈ G(k)` normalizing `L` lies in some
  `g j · L(k)`. Then every irreducible subquotient of `X` is equivalent to the pullback of
  `τ` along `ambientIsoPointsEquiv (φ j)` for some `j`. The index set does not depend on
  `τ`.

## Proof

`pieces_of_supercuspidal` applies the published
`leviJacquetInductionSupercuspidalFiltration` (Renard VI.5.3 (iii) for supercuspidal
inducing data). It supplies a filtration of `X` whose graded pieces are equivalent to
the pullbacks `τ ∘ e_i`, together with the supercuspidality of `X`. The pullbacks are
irreducible (`isIrreducible_pullbackFunctor_obj_iff`), and the filtration lemma above
applies.

In the normalizer form, the conjugating element `z` is written `g j · m` with
`m ∈ L(k)`. `pullbackConjEquiv` then replaces `e_i` by the point map of `φ j`. The two
point maps differ by conjugation by `m`, which is checked through the injective point
map of `lR ≫ r`.

## Provenance and boundary

The filtration is Renard, *Représentations des groupes réductifs p-adiques*, VI.5.3 (iii)
(published `LeviJacquetInductionSupercuspidalFiltrationProof`). The finite set of
representatives is Renard V.4.3.3 (published `leviNormalizerFiniteQuotient`), supplied by
the caller. The module uses only published theorems.
