# Inverse transpose and normalized upper block products

Author: Worker 357.

This pair states an internal transport property of the existing normalized
upper block induction construction. All five declarations are `Prop`-valued
`def` or `abbrev` declarations; the pair supplies no proof of these propositions.
The main target is
`Langlands.Parabolic.InverseTransposeProductStatement`.

## The product clause

`NormalizedProductInverseTransposeClause F T` quantifies over every positive
rank `n`, actual `B : GeneralLinear.BlockShape n`, family of complex module
carriers `V i : Type uV`, and representations `σ i` of `GL_(B.size i)(F)`.
Its only representation-theoretic hypothesis is `∀ i, IsSmooth (σ i)`.
Writing `θ_m(g) = (g⁻¹)ᵗ` and `I_B(σ) = T.normalizedProductInduced B σ`,
its conclusion is

```
Nonempty (Representation.Equiv
  (I_B(σ).comp θ_n)
  (I_(B.reverse)(i ↦ (σ i.rev).comp θ_(B.size i.rev))))
```

Here `comp θ_m` denotes composition with the actual monoid homomorphism
`(GeneralLinear.inverseTranspose m F.Carrier).toMonoidHom`. This is an
existence statement for a complex-linear equivariant equivalence between the
actual induced carriers. No equivalence or alternate induction model is supplied
as a hypothesis. The reversed carrier at `i` is exactly `V i.rev`; the local
additive-group and module instances are the original instances at that index.
The published `B.reverse` has size `B.size i.rev` definitionally, so there is no
replacement block shape or rank cast.

The input factors may be reducible, zero, nonadmissible, or of infinite length.
There is no genericity, irreducibility, admissibility, temperedness, unitarity,
or finite-length assumption. All positive ambient ranks and all their block
shapes are covered, including one-block shapes; positivity of each block size
comes from `B`. The main clause does not include ambient rank zero.

## Required geometry and intended derivation

The provenance is internal: the statement is derived from the concrete
covariance and right-translation definitions in
`Langlands.Representation.Induction.BlockFactors`, together with the actual
matrix constructions in `Langlands.Group.GL.ReverseBlocks`. It is not presented
as the exact wording of a theorem in the original literature. In particular,
the later application to reversed standard-module parameters does not turn
this statement into an identification with the smooth contragredient.

The intended proof must handle both of the following transports.

1. Inverse transpose exchanges the original upper and opposite parabolics.
   This is the published
   `BlockShape.inverseTranspose_mem_oppositeParabolic_iff`.
   For `w = B.reverseMatrix F.Carrier`, conjugation by `w` identifies the upper
   parabolic of `B.reverse` with the original opposite parabolic, as proved in
   `reverseMatrix_conj_mem_oppositeParabolic_iff`. Thus
   `q ↦ θ_n(w q w⁻¹)` sends the reversed upper parabolic into the original
   upper parabolic. At the original block `i.rev`, its diagonal block is
   `θ_(B.size i.rev)(q_i)`.
2. The original tensor carrier `PiTensorProduct ℂ V` must be permuted to
   `PiTensorProduct ℂ (fun i => V i.rev)`, sending the pure tensor with entries
   `v_j` to the pure tensor with entries `v_(i.rev)`. The equivalence in the
   statement compares these actual, possibly different, tensor-valued function
   carriers. This permutation is required even though both finite index sets
   have the same cardinality.

For clarity about the normalization and direction, the intended function map is
`E(f)(g) = P(f(θ_n(w g)))`, where `P` is that tensor permutation. This formula
is explanatory and is not imposed as an additional conclusion of the Lean
statement. Applying inverse transpose to the Levi determinants inverts their
norms; reversing the blocks reverses the modulus exponents. These two changes
make the original positive half-modulus equal to the reversed upper positive
half-modulus. The proof must check that identity for the published
`T.parabolicHalfModulus`, preserve smooth vectors under these continuous
changes of variable, and verify right-translation equivariance and invertibility.
These checks are proof obligations, not premises hidden in this statement.

## Determinant twists and exponent order

`InverseTransposeDeterminantTwistClause F T` states the equality of
representations on the same carrier

```
(twist (T.determinantPowerCharacter n u) σ).comp θ_n
  = twist (T.determinantPowerCharacter n (-u)) (σ.comp θ_n).
```

It holds as a proposed algebraic identity for every natural rank, every
complex representation and every real exponent; smoothness and positive rank
are unnecessary for this small clause. Its provenance is
`det((g⁻¹)ᵗ) = det(g)⁻¹`, the definition of `T.determinantNorm` as the normalized
absolute value of that determinant, and the existing `realPowerCharacter`
and `twist` constructions. Thus the inverse-transpose pullback changes the
real determinant exponent to its negative without changing the carrier.

`ReverseNegateStrictAntiClause` states, for every finite real sequence `u`,
that `StrictAnti u` implies `StrictAnti (fun i => -u i.rev)`.
For `i < j`, reversal gives `j.rev < i.rev`, strict decrease gives
`u i.rev < u j.rev`, and negation gives `-u j.rev < -u i.rev`.
This elementary order calculation includes empty and singleton sequences.

In `Classification.LanglandsData`, `T.twistedBlocks B σ u` is built with
`segmentFactor`, whose representation is precisely the determinant-power
twist above; `twistedProductInduced_representation` identifies its induction
with `normalizedProductInduced`. Applying the product clause to those twisted
blocks and using the twist equality gives reversed blocks pulled back by
inverse transpose with exponents `i ↦ -u i.rev`. The order clause preserves
the decreasing-exponent convention used by `TemperedLanglandsDatum`.
The pair does not construct a new tempered datum or prove preservation of its
other fields.

## Universes, aggregate, and boundaries

`InverseTransposeProductStatement.{uF, uV}` conjoins the product and twist
clauses for every prime `p`, every `F : PadicField.{uF} p`, and every
`T : F.TopologicalData`, with the finite-sequence order clause. The field
universe `uF` and factor-carrier universe `uV` are independent. Both actual
induced carriers lie in `Type (max uF uV)`.

`InverseTransposeProductLiftStatement.{uF, uV, uL}` is an abbreviation for the
same aggregate instantiated at carrier universe `max uV uL`. It therefore
accommodates factors on `ULift.{uL} (V i)` and their induced carriers in
`Type (max uF uV uL)` while keeping `uF`, `uV` and `uL` independent. This is a
universe specialization only: it does not assert an additional equivalence
between lifted and unlifted induction or assume such an equivalence.

The published `NormalizedInductionDualityClause` concerns smooth
contragredients and the same upper parabolic with admissible Levi input.
`TwistedProductOrdinaryDualClause` likewise concerns admissible smooth block
duals in their original order with negated exponents. Those are distinct
assertions. No clause here identifies a reducible standard module with its
smooth contragredient, nor replaces the actual pullback by a dual. No normalized
induction transitivity, adjacent-swap association, or classification theorem is
part of this pair.
