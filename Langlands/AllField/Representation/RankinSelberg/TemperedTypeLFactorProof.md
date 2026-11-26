# JPSS 1983, Proposition (9.4)(3), for tempered-type data over a local field

Module `Langlands.AllField.Representation.RankinSelberg.TemperedTypeLFactorProof`,
namespace `Langlands.AllField.RankinSelberg`.

## Main theorem

```lean
theorem temperedTypeLPolynomial_product
    (hpole : TemperedPoleBoundStatement.{uF, uV, uW} F)
    (htail₁ : InducedTailLFactorAt.{uF, max uF uV, max uF uV, max uF uW} F)
    (htail₂ : InducedTailLFactorAt.{uF, max uF uW, max uF uW, max uF uV} F)
    (ψ) (ν) (d : TemperedTypeDatum.{uF, uV} n) (e : TemperedTypeDatum.{uF, uW} t)
    (hP : IsPadicRankLPolynomial ψ ν.val d.standardModule e.standardModule P)
    (hQ : ∀ i j, IsPadicRankLPolynomial ψ ν.val
      (d.twistedBlock i).representation (e.twistedBlock j).representation (Q i j)) :
    P = ∏ i, ∏ j, Q i j
```

over every nonarchimedean local field `F`: for two data of irreducible tempered blocks of
Whittaker type with antitone real exponents, the L-polynomial of the two standard modules
is the product of the L-polynomials of the pairs of twisted blocks,
`L(s, ξ × η) = ∏_(i,j) L(s, τ_i ν^(u_i) × σ_j ν^(v_j))`. The premises are the pole bound
(8.4) and the tail divisibility (9.3) over `F` (module `TemperedTypePremisesStatement`),
the second for the two universe orders in which it is used.

## Reflection data

`nonempty_temperedTypeReflectedRatioData` and `temperedTypeReflectionData`: certified data
for `(d, e)` and for the reversed inverse-transpose data `(d.inverseTranspose,
e.inverseTranspose)` with `ψ⁻¹` and the same self-dual measure (published all-field
`DominantRankTransport.negatedSelfDualHaar`), and the identity

`D(X) = c X^m E(q⁻¹ / X)`

between the two normalized residuals. The dual certificates are transported to the
inverse-transpose pullbacks by `inverseTransposeStandardModuleEquiv` and
`inverseTransposeTwistedBlockEquiv`; the identity comes from
`TemperedLFactorGamma.nonempty_reflectedRatioData` and the field-free
`TemperedLFactorAlgebra.reflected_identity_of_quotient_ratio`.

## The induction

The proof is the port of the Library's p-adic `langlandsTypeLPolynomial_product`
(module `LanglandsTypeLFactorProof`), with the antitone exponents of `TemperedTypeDatum`
in place of strictly decreasing ones; the p-adic proof uses only antitonicity. A private
proposition `ProductBelow N` states the product formula for all pairs (all characters,
self-dual measures, ranks and data in the fixed universes) with fewer than `N` blocks in
total, and is proved by strong induction.

1. If the second datum has at least two blocks, delete its first block. The tail has fewer
   blocks, so by induction its polynomial is the product `A` of the remaining columns, and
   by `standardTailLPolynomial_dvd` (from `htail₂`, with the pair read in the other order)
   `A` divides `P`. Writing `B = ∏∏ Q = A C` with `C` the first-column product and
   cancelling `A` in `B = D P` gives `D ∣ C`. With one block, `C = B`.
2. Symmetrically, deleting the first block of the first datum (`htail₁`), the residual
   divides the first-row product.
3. By (8.4) (`realPowerTwistRankLPolynomial_poleFree`), every block polynomial `Q i j` has
   no zero in the disk of radius `q^(u_i + v_j)`. Since the exponents are antitone, the
   first-column product, hence `D`, has no zero in the disk of radius
   `q^(u_last + v_first)`.
4. For the reversed data the exponents are `-u_(r+1-i)` and `-v_(s+1-j)`, so by step 2 and
   step 3 applied to them, the dual residual `E` has no zero in the disk of radius
   `q^(-(u_last + v_first))`.
5. The two radii have product one, and `‖q⁻¹‖ < 1` (`norm_residueReflection_lt_one`). The
   published field-free `reflectionRigidity` gives `D = 1` from the reflection identity,
   so `P = B`; uniqueness of certificates transfers this to the given `P` and `Q`.

Source: JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), Proposition (9.4),
display (3), printed page 458, and its proof, printed pages 458–462 (tails, reversed
data, the functional equation, and the pole contradiction at the top of printed
page 462).
