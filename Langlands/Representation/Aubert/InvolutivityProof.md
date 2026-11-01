# Involutivity of the actual unadjusted Aubert operator

Author: Worker 164.

`Langlands.Aubert.involutivity.{uF,uV} F T` proves exactly
`Langlands.Aubert.InvolutivityStatement.{uF,uV} F T`: for every natural
rank `n`, the existing unadjusted endomorphism satisfies

```text
(alternatingOperator F T n).comp (alternatingOperator F T n) = LinearMap.id.
```

The outer parameters are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and supplied `T : F.TopologicalData`.
The field and carrier universes are independent. The equality concerns
every virtual class of the existing exact finite-length smooth complex
Grothendieck group, whose representation carriers have universe
`max uF uV`. All actual short exact sequence relations, including
nonsplit ones, remain in that group. There is no extra hypothesis on the
rank, representation, finite vector-space dimension, admissibility,
central character, irreducibility or cuspidality.

The source statement is Aubert's Theorem 1.7(3), printed p.2181, and the
assembly follows the algebraic route on printed p.2183 of the registered
source `aubert-1995-duality`: Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie
d'un groupe réductif p-adique*, Transactions of the AMS 347 (1995),
2179–2189. The retained PDF has SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The new proof is an internal assembly of the actual-map theorems and
finite cancellation described below.

## Expansion and actual-map comparisons

Write `D_n` for `alternatingOperator F T n`, `i_B` and `r_B` for
`normalizedInductionK0 F T B` and `normalizedJacquetK0 F T B`, and
`ε(B) = (-1 : ℤ)^(n - B.length)`. Linear-map extensionality fixes an
arbitrary virtual class `x`. Expanding the inner operator and distributing
the outer integer-linear map gives

```text
D_n (D_n x) = ∑ B, ε(B) • D_n (i_B (r_B x)).
```

The proved `inductionCommutation` identifies `D_n ∘ i_B` with
`i_B ∘ alternatingOperatorOnLevi F T B`. Applying that map equality to
`r_B x` and expanding the product-Levi operator produces a double sum
over `B` and `S : BlockRefinement B`. Its nested map, in order from
input to output, is coarse Jacquet restriction, refined Jacquet
restriction inside the coarse Levi, induction back to the coarse Levi,
and induction to `GL_n(F)`.

The private pointwise lemma `nestedInductionJacquet_apply` applies
`Parabolic.normalizedComposedInductionK0_comp_composedJacquetK0`
to `x`. By the definitions of the composed maps, it replaces that
four-map composite with `i_C (r_C x)`, where `C = B.flatten S`.
This input is an equality of the actual normalized maps on exact K0.
Its Jacquet comparison uses the representative-preserving equivalence of
the actual flattened upper-radical quotients and the actual coordinate
pullback; its induction comparison uses normalized induction in stages.
Thus the ambient output and the flattened Levi coordinates agree.
Throughout, induction has positive half-modulus covariance and right
translation, and Jacquet restriction has inverse half-modulus Levi
action.

`refinementSignExponent_eq` identifies the product-Levi exponent
`∑ i, (B.size i - (S i).length)` with
`n - (B.flatten S).length`. Linearity and associativity of integer
scalar multiplication therefore identify the expanded square with
`refinementAlternatingSum f` for

```text
f C = normalizedInductionK0 F T C (normalizedJacquetK0 F T C x).
```

The coefficient of each nested term is the unchanged product
`ε(B) * ε(B.flatten S)`.

## Finite cancellation

The helper `refinementAlternatingSum_eq` applies to any function into an
additive commutative group. Its proof uses `refinementCutsEquiv B` to
replace refinements of `B` by flattened shapes `C` satisfying
`B.cuts ⊆ C.cuts`. Exchanging the two finite sums gives coefficient

```text
ε(C) * ∑ B with B.cuts ⊆ C.cuts, ε(B)
```

at `f C`. Cuts identify shapes with subsets of the `n - 1` interior
edges, and `ε(B) = (-1)^(n - 1) * (-1)^B.cuts.card`. Alternating
powerset cancellation makes the coefficient zero unless `C.cuts = ∅`;
the coefficient in that case is one. This yields exactly
`f ((BlockShape.cutEquiv n).symm ∅)`. The finite helpers include rank
zero and use natural-number subtraction with its existing convention.

## The surviving term in every rank

For positive rank, the surviving shape has one block.
`inductionJacquetK0_of_cuts_eq_empty` identifies its actual composite
`i_C ∘ r_C` with `LinearMap.id`. That helper proves the normalized
Jacquet quotient is the original representation after the actual
single-block Levi identification: the radical is trivial and its
modulus is one. Composing with evaluation for the actual single-block
induction gives the representation equivalence, and the exact K0
generator formulas extend it to all virtual classes.

For rank zero the surviving shape is empty. The proof uses
`inductionJacquetK0_rankZero`, whose actual trivial-group induction
evaluation and coinvariant-quotient equivalences establish the same
map identity. Hence the remaining term equals `x` in both cases.
Applying this equality to the arbitrary virtual class finishes
linear-map extensionality.

The proof and its induction-commutation input use the geometric,
finite-length, conjugacy, transitivity and finite combinatorial
infrastructure. Their transitive imports are independent of the
excluded segment classification, multisegment and quotient exhaustion,
ordered strong-head existence, tempered block uniqueness,
square-integrable Langlands classification or exhaustion, and regular
exhaustion. No irreducible-image theorem is used. The target statement
and every pair it imports are unchanged.
