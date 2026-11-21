# Reduction of σ-lift induction to a shared character expansion

`sigmaLiftInductionReduction` proves `SigmaLiftInductionReductionStatement`, an
implication whose conclusion is the Library's unchanged
`Langlands.BaseChange.SigmaLiftInductionStatement`. It uses three premises:

1. `SigmaLiftCharacterIdentityStatement.{u, v, uV, uW}` on the inducing
   representations. The proof uses the direction from σ-lifts (test functions)
   to Shintani lifts (local character values).
2. `SigmaLiftCharacterIdentityStatement.{u, v, max u uV, max v uW}` on the
   induced representations. The proof uses the reverse direction. The carriers
   are spaces of functions on the full general linear groups, which explains
   the two maxima.
3. `SharedInducedCharacterExpansionStatement.{u, v, uV, uW}`, the common
   finite-sum consequence of the ordinary and twisted induced character
   formulas described below.

The theorem constructs the admissibility proofs of the induced representations
using `isAdmissible_normalizedProductInduced`. Its intertwiner witness is
`inducedSigmaIntertwiner σ B A`, with the inverse entrywise action in the
argument of the induced function, as in Henniart–Lemaire II.4.4.

## The expansion premise

Take the cyclic field extension, block shape `B` and rank of the target. For
each associated pair `(δ, γ)` with `γ` regular semisimple, the premise supplies
`k : ℕ`, two families `d : Fin k → B.Levi E` and `g : Fin k → B.Levi F`,
and coefficients `w : Fin k → ℂ`. For each summation index `j` and each block
`i`, `(d j i, g j i)` is associated in the sense of `IsNormAssociated`, and
`g j i` is regular semisimple in that block. The same data must work for all
representations in the following two clauses:

- Given an admissible irreducible family `π` over `F` with irreducible normalized
  product induction, if `a j i` is a local character value of `π i` at `g j i`,
  the induced representation has local character value
  `∑ j, w j * ∏ i, a j i` at `γ`.
- Given an admissible irreducible family `P` over `E` with block σ-intertwiners
  `A` and irreducible normalized product induction, if `b j i` is a local
  twisted character value of `(P i, A i)` at `d j i`, the induced representation
  with `inducedSigmaIntertwiner σ B A` has local twisted character value
  `∑ j, w j * ∏ i, b j i` at `δ`.

Both clauses use the Library's Haar-independent predicates `HasCharacterValue`
and `HasTwistedCharacterValue`. They assert the induced value given the block
values, not the existence of the block values. They impose no lifting condition
on the representations and do not mention the lift scalars. An empty index set
(`k = 0`) gives both induced values zero.

### Provenance and scope

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.4.4–II.4.5, printed
pp. 85–88 (PDF pp. 93–96). In II.4.5, (3) expresses the twisted character of
the induction as a sum of twisted Levi character values over the maps
`η : Z_M(F) → A_T(F)` induced by conjugation; the weight at `η` is
`|D_{G/M}(N(δ)^η)|_F^(-1/2)`. The final paragraph gives the ordinary formula
by setting `E = F` and `σ = id`. In matching these formulas, the summations
are taken using the same rational torus and Levi embeddings, after putting
the associated pair into coordinates with exact norm. The relative
discriminant identity on p. 88 gives the common weight. The character of
the Levi tensor product factors into the block character values. If the
regular norm class misses the Levi, both formulas give vanishing, represented
here by the empty sum. The characterization by Shintani values is HL II.2.9,
Proposition, printed p. 69 (PDF p. 77).

The expansion premise is an internal abstraction of what that comparison
needs. In particular, it does not represent the set of embeddings `η`,
specify the discriminant, assert a formula at arbitrary points, or prove
conjugacy reduction, character factorization, or availability of the expansions.
The equivalence premises are also not proved here.

## Lean proof of the implication

1. Apply the forward equivalence to each factor with its given intertwiner
   and scalar `c i`. This gives `hFactor i : IsShintaniLift … (c i)`. In
   particular each scalar is nonzero, so `Finset.prod_ne_zero_iff` gives
   `∏ i, c i ≠ 0`.
2. For any associated regular pair of the full groups, obtain the common
   expansion data and use `hFactor i` at each paired block argument. `choose`
   gives ordinary values `a j i` and twisted values `c i * a j i` with their
   local-value proofs. Apply the ordinary expansion to `a` and the twisted
   expansion to this product family.
3. Use `Finset.prod_mul_distrib` for each term of the twisted sum and
   `Finset.mul_sum` for the full sum. Commutativity puts the factor `∏ i, c i`
   outside the sum, leaving exactly the ordinary induced value from step 2.
   This is the product Shintani identity. The proof does not require a
   nonempty sum.
4. Use the reverse equivalence on the two irreducible induced representations
   to obtain `IsSigmaLift` with the same product scalar. Together with the
   constructed admissibility proofs and intertwiner, this is the existential
   conclusion of `SigmaLiftInductionStatement`.

The result is conditional and does not prove the unconditional target of
Task 7841.
