# Coefficient linearity of the tensor–Hom and associativity equivalences

The theorem `Langlands.Algebra.tensorHomLinear` proves exactly the published
proposition `Langlands.Algebra.TensorHomLinearTheorem`, with independent universe
parameters `uK`, `uR`, `uS`, `uX`, `uY`, `uZ` in that order. It combines
`unitizedTensorHomLinear` and `nondegenerateTensorHomLinear`. Each of these
packages three clause proofs in the namespace
`Langlands.Algebra.TensorHomLinear`.

The statement and its source interpretation are in
[TensorHomLinearStatements.md](TensorHomLinearStatements.md). The source context
is Renard, *Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, I.2.2, printed pp.15–16 / PDF pp.21–22. This proof is derived from
the published additive equivalences and coefficient comparisons. It does not
reconstruct the source proof through comparison with unitizations. The target
and its imported constructions are used unchanged.

## Scope and hypotheses

The coefficient ring is an arbitrary commutative ring `k`. The algebras `R` and
`S` are arbitrary nonunital rings with compatible `k`-module structures, as
specified in the target. The three unitized clauses use given coefficients on
the carriers, compatible with their original actions. The three nondegenerate
clauses use the precise coefficient modules recovered in the Library from the
idempotented algebra actions.

For the nondegenerate clauses, the published compatibility hypothesis on the
bimodule `Y` is essential to the proof. The right Hom and associativity clauses
use `NonUnitalBimoduleHomScalars.RightSourceCompatible`; the left Hom clause uses
`NonUnitalBimoduleHomScalars.SourceCompatible`. These compare the other algebra
action with the coefficients recovered from `S` on `Y`. The scope is exactly
the corrected proposition in the statement module; the proof makes no claim
about the bare-bimodule coefficient assertion discussed there.

The refined Hom clauses require nondegeneracy of `X` for the additive
factorization into the actual nondegenerate part, and `S`-nondegeneracy of `Y`
and `Z` for compatibility and coefficients. The associativity clause uses
nondegeneracy of `Y` for both actions and of `Z` for `S`; it does not require
nondegeneracy of `X`.

## Unitized Hom clauses

`UnitizedRight.existsLinearCanonical` and
`UnitizedLeft.existsLinearCanonical` start with the published additive
`NonUnitalTensorHomAdjunction.Right.equivalence` and `.Left.equivalence`, applied
to `Unitization k R` and `Unitization k S`. The local unitized actions are
`CompatibleUnitizationTensor.rightNonUnitalModule` and
`.leftNonUnitalModule`. Their commutation is the target module's
`unitizedActionsCommute`.

Each proof equips the same additive equivalence with a `map_smul'` field. After
extensionality in `x` and `y`, coefficient preservation is definitional: both
sides evaluate to `c • φ (x ⊗ y)` in the right clause, or
`c • φ (y ⊗ x)` in the left clause. The coefficient modules here are exactly
`tensorHomModule` and `curriedHomModule` from the statement module. The
corresponding published `equivalence_canonical` theorem supplies the canonical
predicate, including its inverse clauses, because the underlying additive
equivalence has been retained.

## Associativity with given coefficients

The helper `compatibleAssociator_smul` is a derived scalar-preservation lemma
for the published additive associator. It only needs coefficients on `Z`
commuting with the `S`-action, together with the original commuting actions on
`Y`. All tensor coefficients are `NondegenerateTensorScalars.compatibleModule`,
carried through the final factor. The published residual tensor modules and the
statement module's `residual_smulCommClass` make the nested structures available.

For a fixed coefficient `c`, the helper compares two additive maps: composing
the associator after multiplication by `c`, and composing multiplication by `c`
after the associator. `NonUnitalTensorAssociativity.left_hom_ext` reduces their
equality to triple pure tensors. Both values are definitionally
`x ⊗ (y ⊗ (c • z))`. Evaluating the resulting equality of additive maps gives
scalar preservation on every tensor.

`UnitizedAssoc.existsLinearCanonical` applies this helper to the unitized
rings and their commuting actions. It upgrades the same published associator
to a linear equivalence and obtains its canonical predicate from
`NonUnitalTensorAssociativity.associator_canonical`.

## Refined Hom clauses with recovered coefficients

`NondegenerateRight.existsLinearRefinedCanonical` and
`NondegenerateLeft.existsLinearRefinedCanonical` use the published additive
`Right.refinedEquivalence` and `Left.refinedEquivalence`. These already take
values in the exact original nondegenerate part of the residual-action inner
Hom. The ambient additive equivalence is also included, as required by each
`ExistsLinearRefinedCanonical` conclusion.

For coefficient preservation, extensionality at `x` leaves an equality in that
part. Its right side initially uses coefficients recovered from `R` on the
part. The published lemmas
`NonUnitalBimoduleHomScalars.rightSourcePart_recovered_smul_eq` and
`.sourcePart_recovered_smul_eq` identify these with coefficients inherited from
the ambient pointwise Hom module. They apply under exactly the corresponding
compatibility hypothesis on `Y`. Subtype extensionality followed by Hom
extensionality at `y` now reduces the equality to reflexivity. Thus the proof
uses the statement's recovered `refinedHomModule`, rather than substituting a
different coefficient structure in the conclusion.

The published `refinedEquivalence_canonical` theorem proves all remaining
canonical clauses. In particular, it retains the whole-map comparisons after
inclusion into the ambient Hom and the specified comparison of inverse maps.

## Associativity with recovered coefficients

`NondegenerateAssoc.existsLinearCanonical` again upgrades the published
associator. Its source coefficients pass through the coefficients recovered
from `S` on `Z`. Its target coefficients are recovered from `R` on
`Y ⊗_S Z`, which is nondegenerate by
`NondegenerateTensorFunctor.isNondegenerate`.

The proof first applies
`NonUnitalBimoduleTensorScalars.recoveredModule_eq` to identify the entire
`R`-recovered module on `Y ⊗_S Z` with
`NondegenerateTensorScalars.module k S Y Z hS hSZ`. The comparison's
`InputCompatible` requirement is definitionally the supplied
`RightSourceCompatible` hypothesis. This published comparison contains the
compatibility and balancing argument needed to move the coefficient through
the inner tensor.

As in the helper, `left_hom_ext` reduces commutation with each scalar to triple
pure tensors. The source-side value is `x ⊗ (y ⊗ (c • z))`; the target-side value
is `x ⊗ (c • (y ⊗ z))`, with the `R`-recovered inner coefficients. Applying
`congrArg` to the module equality above identifies these expressions. The
resulting equality of additive maps gives scalar preservation on every tensor.
`associator_canonical` then supplies the canonical predicate.

## Assembly

`unitizedTensorHomLinear` packages the three unitized clause proofs.
`nondegenerateTensorHomLinear` introduces the exact hypotheses of the three
published nondegenerate clauses and applies their proofs.
`tensorHomLinear` is their conjunction, with type
`TensorHomLinearTheorem.{uK, uR, uS, uX, uY, uZ}`. All new declarations in this
module are proofs; its mathematical inputs are imported by Lean name.
