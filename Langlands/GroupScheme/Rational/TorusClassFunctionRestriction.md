# Restriction of class functions to the split maximal torus of a pinning

This module applies to a field `k : Type u` of arbitrary characteristic, an
actual affine group scheme `G` over `Spec k`, and a supplied
`p : SplitPinning G`. No algebraic closedness, simple connectedness or
semisimplicity is assumed. All declarations are in namespace
`Langlands.GroupScheme.SplitPinning`. Write `X` for
`characterLattice p.torus` and `k[X]` for `AddMonoidAlgebra k X`.

## The restriction map

`torusUniversalPoint p` is the universal point of the supplied split torus over
`k[X]` from `Langlands.GroupScheme.Torus.SplitCharacterPoint`. Every character `χ`
takes the value `single χ 1` there.

`torusRestriction p : ClassFunctions.algebra G →ₐ[k] k[X]` evaluates an actual
invariant coordinate at the point `torusUniversalPoint p ≫ p.inclusion` of `G`.
So it is restriction along the supplied torus inclusion, written in the monomial
basis of the characters (`torusRestriction_apply`).

- `pointCoordinates_torusPoint`: for every commutative `k`-algebra `A` and every
  point `s` of the torus over `A`, the value of a class function `f` at the image
  point `s ≫ p.inclusion` is obtained from `torusRestriction p f` by `pointLift s`,
  which sends each monomial `single χ r` to `r` times the value of `χ` at `s`. The
  proof writes `s` as a coefficient change of the universal point
  (`affineMap_pointLift`) and uses naturality of point coordinates.
- `pointCoordinates_torusPoint_eq_zero`: if the torus restriction of `f` is zero,
  then `f` vanishes at the image of every torus point over every algebra.

## Invariance under root reflections

`torusRestriction_coeff_reflection`: for every class function `f`, every root
index `α` and every weight `ν`, the coefficient of `torusRestriction p f` at
`p.rootDatum.reflection α ν` equals its coefficient at `ν`.

The proof uses the published `IsRootDatumOf` field of the pinning. It supplies a
rational point `n` of `G` and an automorphism `σ` of the torus with
`IsNormalizingPoint p.inclusion n σ` and `characterAut σ = reflection α`. Since the
reflection is an involution, `reflection α χ = σ.hom ≫ χ` for every character.
Let `u` be the universal point and `s = u ≫ σ`. Conjugating the image of `u` in
`G` by the constant point `n` gives the image of `s` (`comp_innerIso_hom` and the
normalizing equation). Conjugation invariance of `f` on `k[X]`-points
(`ClassFunctions.mem_algebra_iff_invariant`) and `pointCoordinates_torusPoint`
therefore give `pointLift s (torusRestriction p f) = torusRestriction p f`. The
character values at `s` are the monomials `single (σ.hom ≫ χ) 1`, so `pointLift s`
is the algebra automorphism `AddMonoidAlgebra.domCongr` of `k[X]` induced by the
reflection. Comparing coefficients gives the claim.

## Trace characters

For a matrix representation `ρ : MatrixRepresentation G n`,
`torusUniversalMatrix p ρ` is the matrix of `ρ` at the image of the universal torus
point, and `torusRestriction_traceClassFunction` says that the torus restriction of
the actual trace class function is its trace.

- `torusUniversalMatrix_mulVec_of_mem`: a vector of the published weight space
  `p.representationWeightSpace ρ ξ` is an eigenvector of this matrix with
  eigenvalue `single ξ 1`. This is the Library's all-algebra character equation
  `characterSpace_affine` at the universal point, together with
  `value_universalPoint`.
- `coeff_mulVec_algebraMap`: taking the coefficient at `ν` of a matrix-vector
  product with a vector of constants is the product with the coefficient matrix.
- `torusRestriction_traceClassFunction_coeff`: if the weight spaces of `ρ` span
  the whole coordinate space, then for every `ν` the coefficient of the torus
  restriction of the trace of `ρ` at `ν` is the dimension of the weight space at
  `ν`, as an element of `k`. Let `N` be the coefficient matrix at `ν` of the
  universal torus matrix. By the eigenvector equation, `N` fixes the weight space
  at `ν` and kills every other weight space. Since the weight spaces span, `N` is a
  projection onto the weight space at `ν` (Mathlib's `LinearMap.IsProj`), and
  Mathlib's `LinearMap.IsProj.trace` computes its trace as that dimension. The
  coefficient of the trace is the trace of the coefficient matrix.

For a supplied fundamental representation `F : p.FundamentalRepresentation a`,
the published `IsHighestWeight` conjuncts give the following.

- `torusRestriction_character_coeff_highestWeight`: the torus restriction of
  `F.character` has coefficient `1` at `F.highestWeight`, because the highest
  weight space has dimension one.
- `sub_mem_positiveRootMonoid_of_mem_support`: every weight in the support of the
  torus restriction of `F.character` lies below the highest weight, that is,
  `F.highestWeight - ν ∈ p.positiveRootMonoid`. A weight with nonzero coefficient
  has a nonzero weight space, and the published bound applies.

## Provenance

The restriction of regular class functions to the maximal torus, its invariance
under the Weyl group, and the expression of a character on the torus as a sum of
weights with multiplicities are the setting of Steinberg 1965, §6, statement
before Lemma 6.2 and the proof of Lemma 6.3 (printed pp. 62–63, PDF pp. 15–16).
Steinberg works with points of an algebraic group over an algebraically closed
field. This module is a derived translation to the actual scheme-theoretic
invariant coordinate algebra and to all test algebras. Weyl invariance is proved
only for the reflections supplied by the pinning's root-datum predicate, which is
what the root-datum combinatorics needs. The multiplicity formula is proved from
the published weight-space definitions, without irreducibility. The module does
not prove that the restriction is injective or that its image is the whole
invariant algebra.
