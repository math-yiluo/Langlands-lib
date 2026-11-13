# H-quasi-projective schemes over an affine base

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705),
with the interface agreed with Worker 5705.

## Definition

`Langlands.AlgebraicGeometry.IsHQuasiProjective p` is a proposition about a
morphism of schemes `p : X ⟶ Spec (CommRingCat.of A)`, for a commutative ring
`A : Type u`. It holds when there are

- a natural number `n`,
- a morphism `i : X ⟶ ProjectiveSpace A n` such that `IsImmersion i` and
  `QuasiCompact i` hold, and
- the equation `i ≫ projectiveSpaceToSpec A n = p`.

So `X` is a locally closed subscheme of finite projective space over `A`,
embedded compatibly with the given structure morphism, by a quasi-compact
immersion. `ProjectiveSpace A n` and `projectiveSpaceToSpec A n` are the
Library's projective space `Proj A[x₀, …, xₙ]` and its structure morphism, from
`Langlands.AlgebraicGeometry.ProjectiveSpace`. The definition is the immersion
analogue of the Library's `IsHProjective`, which asks for a closed immersion
in the same position.

## Source

This is the H-quasi-projective notion of the Stacks Project, specialised to an
affine base `Spec A` and to the Library's model of `P^n_A`. Stacks defines a
morphism `X → S` to be H-quasi-projective when there is a quasi-compact
immersion `X → P^n_S` over `S`. The definition is in Section 29.41
(Quasi-projective morphisms), which is not among the retained pages. The
retained snapshot `stacks-projective-space-twists-morphisms-2026-10-26`
(`01W7.html`, Section 29.44) restates it in the proof of Lemma 29.44.11 ("By
definition we can factor `f` as a quasi-compact immersion `i : X → P^n_S`
followed by the projection"). The same snapshot proves that an H-projective
morphism is H-quasi-projective (Lemma 29.44.3). It also proves that over a
base with an ample invertible sheaf, in particular an affine base, every
quasi-projective morphism in the sense of EGA is H-quasi-projective (Lemma
29.44.16). So over `Spec A` the definition agrees with the EGA notion of
quasi-projectivity.

N. Nitsure, *Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`, p.23), calls this the
strongest version of quasi-projectivity, the one used by Hartshorne: a locally
closed embedding into `P^n_S`. Over a noetherian ring `A` the scheme
`ProjectiveSpace A n` is noetherian, so every immersion into it is
quasi-compact, and the clause `QuasiCompact i` adds nothing there.

## Use

Statements in the Picard construction of Task 5705 use this predicate as their
notion of quasi-projectivity over a noetherian ring. Examples are
`FlatProperEquivalenceRelationQuotientStatement` and
`Picard.RelativeEffectiveDivisorHilbertPiecesStatement`. From a witness `i`,
the published Library theorems
`PointTopology.hasFiniteAffineNeighborhoods_of_projectiveImmersion` and
`PointTopology.isSeparated_of_projectiveImmersion` give finite affine
neighbourhoods and separatedness. The module proves no lemmas about the
predicate.
