# Semisimplicity of polynomial functions under a reductive group

Authors: Worker 1359 and Worker 1571.

This module proves two consequences of the published characteristic-zero
complete reducibility theorem
`Langlands.GroupScheme.reductiveCharZeroSemisimplicityStatement`. That theorem
says that, over an algebraically closed field `k` of characteristic zero, the
rational representation of every matrix representation of a pseudo-reductive
group scheme `G` is semisimple. The consequences are:

- the substitution action of the rational points of `G` on polynomials
  `MvPolynomial κ k`, through any matrix representation `σ` with index type
  `κ`, is semisimple (`isSemisimpleRepresentation_polyRep`);
- right translation on polynomial functions of a pair of `n × n` matrices,
  restricted to the image of the `k`-points of `G` under a matrix
  representation `ρ`, is semisimple
  (`isSemisimpleRepresentation_rightTranslation`).

The second result supplies the semisimplicity hypothesis
`[Representation.IsSemisimpleRepresentation (subgroupRep H)]` of the closed
orbit theorem `Langlands.Group.ClosedOrbit.exists_conj_star_mem` of Worker
1571. That module is a separate staged candidate and is not imported here. Over
an `RCLike` field its `subgroupRep H` is right translation by
`subst (rightMatrix h)` with `subst M = bind₁ fun i => ∑ j, M i j • X j`. Here
`polyRep (rightHom k n) h` is `bind₁ fun i => ∑ j, (rightMatrix h)ᵀ j i • X j`.
The `rightMatrix` of this module is defined by the same formula, so the two
substitutions agree entry by entry.

## Representations

These results hold for a field `k`, a group `G` and a `k`-module `V`.

- `isSemisimpleRepresentation_of_comp`: if `π : G' →* G` is surjective and
  `ρ.comp π` is semisimple, then `ρ` is semisimple. Both representations have
  the same invariant subspaces, and the proof transfers complements along the
  resulting order isomorphism of subrepresentation lattices.
- `map_asAlgebraHom`: a `k`-linear map that commutes with the group actions
  also commutes with the group-algebra actions `asAlgebraHom`.
- `isSemisimpleRepresentation_of_cover`: suppose a family of semisimple
  representations `τ i` maps to `ρ` by equivariant linear maps `φ i`, and every
  vector of `V` is a value of some `φ i`. Then `ρ` is semisimple. The proof
  passes to modules over the group algebra `k[G]`. There the images of the
  `φ i` are semisimple submodules whose supremum is everything, and Mathlib's
  `isSemisimpleModule_of_isSemisimpleModule_submodule'` applies.

## Matrices

These constructions work over any commutative ring `A`. Each one commutes with
ring homomorphisms (the lemmas ending in `_map`).

- `kroneckerPower D M`: the `D`-fold Kronecker power of a square matrix,
  indexed by words `Fin D → κ`, with entry `∏ t, M (e t) (e' t)` at `(e, e')`.
  The lemmas `kroneckerPower_mul` and `kroneckerPower_one` show that it is
  multiplicative and unital.
- `padded M`: the block matrix `fromBlocks M 0 0 1` on `κ ⊕ Unit`. It extends
  `M` by the identity on one padding coordinate and is multiplicative and
  unital.
- `wordHom A κ D : GL κ A →* GL (Fin D → κ ⊕ Unit) A`: the group homomorphism
  `g ↦ kroneckerPower D (padded g)` (`coe_wordHom`).
- `rightMatrix h`: for `h : GL n A`, the matrix on the entries
  `(n × n) ⊕ (n × n)` of a pair of matrices whose action on coordinate vectors
  is `(X, Y) ↦ (X h, h⁻¹ Y)`. It is
  `fromBlocks (1 ⊗ₖ hᵀ) 0 0 (h⁻¹ ⊗ₖ 1)`. It reverses products
  (`rightMatrix_mul`) and sends `1` to `1`.
- `rightHom A n : GL n A →* GL ((n × n) ⊕ (n × n)) A`: the group homomorphism
  `h ↦ (rightMatrix h)ᵀ` (`coe_rightHom`). The transpose makes it preserve
  products.

## Polynomials

These results hold over a field `k` and a finite index type `κ`.

- `linearSubst M`: the algebra endomorphism of `MvPolynomial κ k` given by
  `X i ↦ ∑ j, M j i • X j` (`linearSubst_X`). It sends `1` to the identity and
  products of matrices to composites (`linearSubst_one`, `linearSubst_mul`).
- `polyRep π`: for a group homomorphism `π : Γ →* GL κ k`, the representation
  of `Γ` on `MvPolynomial κ k` in which `g` acts by `linearSubst (π g)`
  (`polyRep_apply`, `polyRep_eq`).
- `letter`: the variables `X i` together with the constant `1` for the padding
  letter. `wordMonomial e` is the product `∏ t, letter (e t)` spelled by a
  padded word `e : Fin D → κ ⊕ Unit`.
- `linearSubst_letter` and `linearSubst_wordMonomial`: substituting by `M`
  sends a letter to its combination by the column of `padded M`. It sends a
  word monomial to
  `∑ e', kroneckerPower D (padded M) e' e • wordMonomial e'`.
- `exists_wordMonomial_eq`: every monomial `monomial α 1` of degree at most `D`
  is a word monomial of length `D`. Unused positions of the word carry the
  padding letter.
- `wordMap k κ D`: the linear map from functions on words of length `D` to
  polynomials that sends `c` to `∑ e, c e • wordMonomial e`.
- `exists_wordMap_eq`: every polynomial of total degree at most `D` is a value
  of `wordMap k κ D`.
- `wordMap_mulVec`: `wordMap` sends `kroneckerPower D (padded M) *ᵥ c` to
  `linearSubst M (wordMap c)`. That is, it intertwines the Kronecker power of
  the padded matrix with linear substitution.

## Group-scheme homomorphisms

These definitions use a base ring `R : CommRingCat`. The Kronecker power and
right translation constructions are natural in the coefficient ring, so they
define natural transformations of the general linear group functors
(`wordNat`, `rightNat`). Through the published
`Langlands.GroupScheme.Corepresented.groupSchemeMap` and the corepresentability
of `GeneralLinear.functor` they become actual homomorphisms of group schemes:

- `wordGroupHom R κ D : GeneralLinear.groupScheme κ R ⟶
  GeneralLinear.groupScheme (Fin D → κ ⊕ Unit) R`;
- `rightGroupHom R n : GeneralLinear.groupScheme n R ⟶
  GeneralLinear.groupScheme ((n × n) ⊕ (n × n)) R`.

Composing a matrix representation with these homomorphisms gives
`wordRepresentation D σ` and `rightRepresentation ρ`. On points they are
computed by `wordHom` and `rightHom`: see `pointMatrix_wordRepresentation`,
`pointMatrix_rightRepresentation`, and, for rational points,
`rationalMatrix_wordRepresentation` and `rationalMatrix_rightRepresentation`.

## Main results

Let `k : Type u` be an algebraically closed field of characteristic zero and
`G` a group scheme over `Spec k` with `IsPseudoReductive G`.

- `isSemisimpleRepresentation_polyRep`: for every matrix representation `σ`
  of `G` with index type `κ`, the representation `polyRep σ.rationalMatrix` of
  the rational points of `G` on `MvPolynomial κ k` is semisimple.
- `isSemisimpleRepresentation_rightTranslation`: for every matrix
  representation `ρ` of `G` of size `n`, let
  `H = (ρ.affineMatrix (CommAlgCat.of k k)).range`. This is the subgroup of
  `GL n k` consisting of the matrices of the `k`-points of `G`. Then the
  representation `(polyRep (rightHom k n)).comp H.subtype` of `H` on
  `MvPolynomial ((n × n) ⊕ (n × n)) k` is semisimple.

## Proof

For `isSemisimpleRepresentation_polyRep`, fix `D`. The published
semisimplicity theorem applies to the matrix representation
`wordRepresentation D σ`, so its rational representation on functions on words
of length `D` is semisimple. By `rationalMatrix_wordRepresentation` and
`wordMap_mulVec`, the map `wordMap k κ D` is equivariant from this
representation to `polyRep σ.rationalMatrix`. Every polynomial is in the image
of `wordMap k κ (totalDegree p)` (`exists_wordMap_eq`). So
`isSemisimpleRepresentation_of_cover` gives semisimplicity.

For `isSemisimpleRepresentation_rightTranslation`, the rational points of `G`
map onto `H`. The map is `ρ.rationalMatrix` restricted to `H`. It lands in `H`
and is surjective by the published comparison
`Langlands.Plancherel.rationalMatrix_eq_affineMatrix` and the
equivalence `Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv`. Composing the representation of `H` with this
surjection gives `polyRep (rightRepresentation ρ).rationalMatrix`, by
`rationalMatrix_rightRepresentation`. That representation is semisimple by the
first result, and `isSemisimpleRepresentation_of_comp` transfers
semisimplicity back to `H`.

## Provenance

The statements and proofs are internal. The fact that polynomial functions on
a representation of a linearly reductive group form a semisimple
representation is classical. Here it is derived only from the published
complete reducibility theorem. Each degree-bounded piece of polynomials is the
image of a Kronecker power of `σ` padded by a trivial line. No literature
statement is formalized. The padded-word technique and the proofs of
`letter`, `wordMonomial`, `exists_wordMonomial_eq` and the span argument of
`exists_wordMap_eq` are adapted from Worker 1571's closed-orbit module
`Langlands.Group.ClosedOrbit`, rewritten over a general field and a general
index type.
