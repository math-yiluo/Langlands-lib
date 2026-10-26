# A radical character witness outside the open GL orbit

Author: Worker 179. Mathematical specification and proposed elementary-root
route: Worker 330.

`Langlands.Whittaker.NonOpenCharacterWitnessStatement` is a proposition
definition, with no proof supplied here. It quantifies a field `K : Type uK`
in an arbitrary universe, a positive total rank `n + 1`, an actual
`BlockShape (n + 1)`, and a raw additive character `ψ : AddChar K ℂ` with
`ψ ≠ 1`.

For every actual finite permutation subtype element

```lean
v : Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1))
```

different from `B.reversePermutation.symm`, put `P = B.parabolic K`,
`U = GeneralLinear.upperUnipotent (n + 1) K`, and
`w = GeneralLinear.permutation (n + 1) K v.val`. The assertion is the existence
of `q : Geometric.orbitStabilizer P U w` such that

```lean
B.leviProjection K (Geometric.stabilizerToInducing P U w q) = 1
entrywiseCharacter ψ (n + 1) q.val ≠ 1
```

These conditions hold for the same `q`. The second inequality is in `ℂˣ`.
Its complex value is `ψ` evaluated on the sum of the first-superdiagonal
entries, by the imported `entrywiseCharacter_apply_sum`.

## Actual groups and conventions

The orbit convention is `P * w⁻¹ * U`. The existing stabilizer is a subgroup
of `U` whose membership condition is `w⁻¹ * q * w ∈ P`.
`Geometric.stabilizerToInducing` sends `q` to this conjugate in `P`.
The existing `B.unipotentRadical K` is the kernel of `B.leviProjection K`,
so the first equality places the conjugate in that original radical.
No replacement stabilizer, Levi, permutation set, or character is introduced.

`B.reversePermutation` sends reversed-shape coordinates to original-shape
coordinates. The excluded representative is its inverse: it sends the
original blocks to their reversed positions, preserving the order of
coordinates within each block. It need not equal `B.reversePermutation`;
for sizes `(1,2)`, the latter has images `(1,2,0)` and its inverse has
images `(2,0,1)`. Neither the full coordinate reversal nor the uninverted
block permutation replaces the specified representative.

The word “non-open” names the usual orbit distinction. The formal premise
is exactly inequality with this distinguished permutation; the proposition
contains no topology or separate openness predicate. In particular, there
are no continuity, norm-one, admissibility, representation, or irreducibility
hypotheses, and no assumed combinatorial witness or character incompatibility.

## Source and derived provenance

The source is François Rodier, *Modèles de Whittaker des représentations
admissibles des groupes réductifs p-adiques quasi-déployés*, retained
46-page author manuscript, Chapter V.2. The setup and Theorem 4 are on PDF
page 36 (manuscript page 37); Lemma 6 and its proof are on PDF page 37
(manuscript page 38). The character and distribution reductions in the
proof of Theorem 4 are on PDF pages 38–42. All seven PDF pages were read
and visually checked for this statement.

Registered source: `rodier-whittaker-author-manuscript`.
Retained file:
`/home/taskhub/central-library/Rodier--Modeles de Whittaker des representations admissibles des groupes reductifs p-adiques quasi-deployes--1975/Rodier--Modeles de Whittaker (author manuscript).pdf`.
SHA256:
`8c110b6b626108ec67421f288baa4b761a8073df2c68db6be8360b654f569812`.
The adjacent source README describes the author's modified 1975 version and
the scan's possible pagination gaps. This is not the six-page 1973 proceedings
article. No source-specific erratum note was found in the checked project,
Library, or literature notes.

Lemma 6 says that triviality of the principal character on
`U ∩ w V w⁻¹`, where `V` is the parabolic radical, forces the double coset
`U w P` to be the distinguished open one. Its proof examines simple roots:
the radical cannot carry a simple root detected by the principal character
under the triviality assumption. The resulting root inclusions force the
distinguished double coset. Inverting the source's double cosets gives the
project's `P w⁻¹ U` convention; this changes the orbit presentation, not the
chosen ambient character or its sign.

The present statement is a derived GL matrix refinement of that root-character
criterion. Rodier works in a p-adic setting and introduces an admissible
irreducible inducing representation for Theorem 4. He does not literally
state the arbitrary-field, raw-additive-character proposition above.

The intended future proof can be entirely algebraic. Read the original block
labels along the ambient positions, namely
`Geometric.blockIndex B (v.val.symm a)`. If no adjacent labels strictly
increase, this finite sequence is nonincreasing. Every original block occurs
with its prescribed multiplicity, so its labels must then occur as consecutive
blocks in reverse order. Minimality says that `v.val` preserves order within
each original block; it consequently determines the positions inside those
blocks as well, forcing `v.val = B.reversePermutation.symm`. The singleton
part of the minimality condition introduces no further ordering restriction.
Thus the excluded equality gives adjacent ambient positions whose inverse
images lie in strictly increasing original blocks.

Choose `t : K` with `ψ t ≠ 1`, using `ψ ≠ 1`, and put `t` in that elementary
upper root subgroup: the matrix is `1 + t Eᵢ,ᵢ₊₁`. Its inverse is
`1 - t Eᵢ,ᵢ₊₁`, so it is an actual upper-unipotent element. Conjugating by
`w⁻¹` puts its sole off-diagonal entry between strictly increasing original
blocks. Hence it is in `P` with identity diagonal blocks, and its original
Levi projection is one. The ambient character has complex value `ψ t`, so
detects it without changing the character sign. This is the proposed proof
route, not a Lean proof supplied by this pair.

## Boundary with induced localization

Theorem 4's source argument passes through distributions on `U × P`, on
`P`, and on the Levi, using covariance and radical invariance; it then
eliminates non-open orbit distributions and treats restriction and extension
on the open orbit. Those steps contain more than the root witness.

The proposition here asserts only the common radical/character witness.
Such a witness has trivial action in a representation inflated through the
Levi projection, but vanishing of a whole induced localization quotient
also requires the separate compact-induction character comparison and its
localization argument. This pair states no quotient vanishing, comparison
isomorphism, induction heredity, or Whittaker uniqueness theorem.
