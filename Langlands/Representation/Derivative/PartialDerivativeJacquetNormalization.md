# Actual determinant normalization for the positive Jacquet comparison

Author: Worker 593.

This module supplies the scalar part of the positive two-block
Jacquet-to-derivative comparison. It constructs composite quotient maps into
the existing derivative objects and proves their surjectivity, naturality
and normalized action formulas. It then identifies the accumulated scalar
with the inverse-half of the existing two-block modulus on the first factor.
The three basic determinant lemmas are shared through the paired
`MirabolicDeterminant` module, with their original names and proofs preserved.

The namespace is `Langlands.Derivative.JacquetNormalization`. The principal
construction is `generalLinearDerivativePositiveMk.{uF,uV}`; the final action
identity is
`generalLinearDerivativePositive_action_mk_eq_inverseHalf.{uF,uV}`. These
results are a focused helper for task
`a4119dcc-97b6-47e4-b150-d5e97a8f226b`, not a proof of
`Langlands.Derivative.PartialDerivativeJacquetComparisonStatement`.

## Parameters and actual carriers

The matrix lemmas use any commutative ring `R : Type uF`, with all natural
ranks and no nontriviality assumption. The normalization and representation
constructions use

```
{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
(T : F.TopologicalData)
(ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
```

Every representation construction installs exactly `T.topology`. The
categories are the existing `SmoothRep.{0,uF,uV} ℂ _`, with `uF` and `uV`
independent. The original carrier and every quotient stay in `Type uV`.
There is no topology on a representation carrier, dimension restriction,
finite length, admissibility, irreducibility or genericity assumption.
Every morphism in these categories is covered.

## Actual embeddings and determinants

`determinant_blockSum` proves that the determinant of the actual
`GeneralLinear.blockSum (g,h)` is the product of the determinants. It unfolds
the actual block matrix and uses Mathlib's `det_reindex_self` and
`det_fromBlocks_zero₂₁`. The determinant of the scalar identity is one, so
`determinant_levi` proves that the actual `Mirabolic.levi g = diag(g,1)`
preserves determinant. `determinant_successor` applies the same fact to
`Mirabolic.successor`, which is `levi` after the actual subgroup inclusion.
These elementary matrix identities now reside in the imported
`MirabolicDeterminant` pair; their proofs use only the actual matrix
constructions and Mathlib determinant identities.

`successorIterate n j` is the actual homomorphism

```
mirabolic n R →* mirabolic (n+j) R
```

defined by the identity for `j=0`, and by one more actual `successor` at the
successor case. `determinant_successorIterate` proves determinant
preservation by induction. `generalLinearToMirabolic n j` composes it with
the actual `levi : GL_n →* mirabolic n`. Its determinant is that of the
original `GL_n` matrix.

`rankInclusion_succ` proves that appending one identity coordinate after an
identity block agrees with the actual larger identity block. The proof
compares matrix entries, first separating the original `n` coordinates from
the `j+1` identity coordinates, and then separating the final coordinate of
the identity block. Consequently `generalLinearToMirabolic_val` proves the
literal equality

```
(generalLinearToMirabolic n j g).val =
  GeneralLinear.rankInclusion (j+1) g.
```

Thus the acting matrix in the original ambient representation is precisely
`diag(g,I_(j+1))`; it is not a supplied comparison of embeddings.

## One half determinant at each actual step

Write `ν_n = T.determinantNorm n`. It is the published residue-normalized
absolute value of the actual determinant. Applying `T.normalizedAbsUnits` to
the determinant equalities proves `determinantNorm_levi` and
`determinantNorm_successorIterate`.

The existing minus functors use the actual characters

```
Mirabolic.psiMinusCharacter T n =
  realPowerCharacter ν_n (-(1/2 : ℝ))
Mirabolic.phiMinusCharacter T n =
  realPowerCharacter
    ((ν_(n+1)).comp (mirabolic n F.Carrier).subtype) (-(1/2 : ℝ)).
```

`phiMinusCharacter_successorIterate` proves that evaluating the latter
character after the actual successor tower leaves it unchanged.
`phiMinusCharacter_levi` proves that its actual Levi pullback equals
`psiMinusCharacter T n`. Both results follow by the proved determinant-norm
equalities and the definition of `realPowerCharacter`. They do not assume a
compatibility of normalization characters.

`psiMinusCharacter_eq_inverseHalf` identifies the actual real-power
character with `Jacquet.inverseHalfCharacter ν_n`. Its proof compares complex
values, uses the positive real square root, and applies
`Real.sqrt_eq_rpow` and `Real.rpow_neg`. This verifies the sign and the
magnitude without choosing a complex square-root branch.

For positive `k,m`, `leviModulus_first` applies the published
`T.leviModulus_twoBlocks` to the inverse of the actual ordered Levi
equivalence at `(g,1)`. The denominator is one, giving exactly `ν_k(g)^m`.
Taking the canonical positive inverse square root and using multiplicativity
of `NNReal.sqrtHom` gives `inverseHalf_leviModulus_first`:

```
Jacquet.inverseHalfCharacter (T.leviModulus (twoBlocks k m hk hm))
    ((twoBlockLeviEquiv hk hm F.Carrier).symm (g,1)) =
  Mirabolic.psiMinusCharacter T k g ^ m.
```

In particular the first-factor normalization is retained. It is the inverse
half of `|det(g)|^m`, commonly written `|det(g)|^(-m/2)`.

## Composite maps into the existing quotients

`phiStepMk T ψ n A` is definitionally
`Mirabolic.phiMinusQuotient T ψ n A`, with its codomain written as the actual
object `(Mirabolic.phiMinus T ψ n).obj A`. This typing wrapper changes no
map, relation or carrier. Its surjectivity, naturality and normalized action
formula are the existing one-step quotient laws.

`phiIterateMk T ψ n j A` composes those actual quotient maps into
`(phiMinusIterate T ψ n j).obj A`. For `j=0` it is the identity linear map.
For `j+1` it first applies the actual quotient at the largest rank `n+j`,
then the already constructed `j`-step map. This is the same order as the
published recursive functor. The zero and successor evaluation identities,
surjectivity and naturality are proved.

Specifically `phiIterateMk_natural` says, for every actual intertwiner
`f : A ⟶ B`,

```
SmoothRep.hom ((phiMinusIterate T ψ n j).map f)
    (phiIterateMk T ψ n j A v) =
  phiIterateMk T ψ n j B (SmoothRep.hom f v).
```

The induction uses the actual mapped intertwiner of `Mirabolic.phiMinus`
and its one-step quotient formula; no replacement functor is introduced.

`phiIterate_action_mk` proves the corresponding normalized action:

```
((phiMinusIterate T ψ n j).obj A).representation h
    (phiIterateMk T ψ n j A v) =
  (Mirabolic.phiMinusCharacter T n h : ℂ)^j •
    phiIterateMk T ψ n j A
      (A.representation (successorIterate n j h) v).
```

At each successor step, the existing `phiMinus_action` formula supplies its
actual determinant half. The proved
`phiMinusCharacter_successorIterate` identifies its restriction with the
smaller character. Linearity moves that scalar through the remaining
quotient map, and `pow_succ` collects the factors.

`mirabolicDerivativeMk` follows `phiIterateMk` with the actual
`Mirabolic.psiMinusQuotient`. It lands in the existing
`(mirabolicDerivative T ψ n j).obj A`, and its surjectivity and naturality
follow by composition. `mirabolicDerivative_action_mk` uses the actual
`psiMinus_action`, the just-proved Phi action formula, and
`phiMinusCharacter_levi`, to obtain

```
((mirabolicDerivative T ψ n j).obj A).representation g
    (mirabolicDerivativeMk T ψ n j A v) =
  (Mirabolic.psiMinusCharacter T n g : ℂ)^(j+1) •
    mirabolicDerivativeMk T ψ n j A
      (A.representation (generalLinearToMirabolic n j g) v).
```

Thus the `j` Phi steps and the final Psi step contribute exactly `j+1`
halves on the actual iterated quotient, for every original vector.
Surjectivity ensures that these are action formulas on every vector of the
derivative, not on a selected subspace.

`generalLinearDerivativePositiveMk` applies that map to the actual
`generalLinearRestriction` of `A`. Restriction retains the original carrier
and underlying linear map. Its surjectivity and naturality therefore have
the same formulas for the existing `generalLinearDerivativePositive`.
`generalLinearDerivativePositive_action_mk` substitutes
`generalLinearToMirabolic_val` in the preceding formula. Its original action
is exactly `A.representation (rankInclusion (j+1) g)`.

Finally `generalLinearDerivativePositive_action_mk_eq_inverseHalf`, for
`hk : 0 < k`, replaces that power by the inverse-half two-block scalar with
`m = j+1`. It uses the actual continuous equivalence
`twoBlockLeviContinuousEquiv`, whose underlying group equivalence is the one
in `inverseHalf_leviModulus_first`. The output action formula is

```
((generalLinearDerivativePositive T ψ k j).obj A).representation g (q_A v) =
  (Jacquet.inverseHalfCharacter
      (T.leviModulus (twoBlocks k (j+1) hk (Nat.succ_pos j)))
      ((twoBlockLeviContinuousEquiv hk (Nat.succ_pos j) F.Carrier).symm
        (g,1)) : ℂ) •
    q_A (A.representation (rankInclusion (j+1) g) v).
```

Here `q_A` is exactly `generalLinearDerivativePositiveMk T ψ k j A`.
There is no equivariance or normalization hypothesis in this identity.

## Source motivation and provenance

The constructions and proofs above are internal derivations from the
published functors, matrix embeddings and positive characters. They
formalize the scalar bookkeeping required by Zelevinsky's comparison; they
are not separately stated results attributed to the originals.

Zelevinsky, *Induced representations of reductive p-adic groups II.
Irreducible representations of GL(n)* (1980), §3.7 and Proposition 3.7(b),
printed page 182 / one-based PDF19, identifies the ordinary `m`-th
derivative with the partial derivative of the normalized `(k,m)` Jacquet
module. The source cites the derivative definition and BZ77 1.9(c),(g).
Only this comparison motivates the helper. The neighboring segment
derivative theorem on the same page is not used.

- Literature ID: `zelevinsky-1980-induced-ii`.
- SHA256:
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- Retained original:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §1.8(b), printed pages 444–445 / PDF5–6, uses the inverse half of
the positive conjugation modulus on the relation quotient.
Proposition 1.9(c),(g), printed page 445 / PDF6, records transitivity and
tensor compatibility. Section 3.5, printed page 452 / PDF13, defines the
positive derivative as `Ψ⁻ ∘ (Φ⁻)^(m−1)`, with larger ranks first.
Section 4.3, printed page 454 / PDF15, first restricts a general-linear
representation to the actual mirabolic subgroup.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- SHA256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

All the specified pages were read and visually inspected, including the
negative exponent on BZ77 printed page 444. Both source hashes were checked
against the retained PDFs. No source-specific errata file was found in the
supplied project literature, current public notes or central-library file
listing; this is a bounded check.

## Scope and remaining comparisons

The representation formulas use precisely the published explicit
determinant-normalized minus functors and the published algebraic
two-block modulus. This helper does not identify a character with a Haar
conjugation modulus. It imports no Haar-modulus proof, and no Haar
identification is assumed in any proof here.

It also does not prove an iterated character-localization equivalence,
identify the combined localizing subgroups or their characters, compare
relation subspaces, construct an inverse quotient comparison, or construct
the natural Jacquet-to-derivative isomorphism. Those are still required by
the parent exact proof task. In particular the separately owned tower
construction `8656acbe-5ee9-4186-a79a-68d661771ada` is not imported or
duplicated.

All `n,j ≥ 0` are allowed in the quotient and action helpers. The modulus
identity requires positive `k,m`, as the current `BlockShape` does.
These facts construct neither the separately owned `k=0` top-localization
comparison nor the `m=0` identity/partial-zero adapter. No arbitrary
representation carrier of `GL_0` is replaced by a one-dimensional carrier.
There is no tensor comparison, product or Leibniz filtration, plus functor,
adjunction, duality, pairing, segment theorem or classification assertion.

## Imports and independence audit

The only direct project imports are
`Langlands.Representation.Derivative.Iteration` and
`Langlands.Representation.Shahidi.TwoBlocks`, whose complete current pairs
were read. The actual transitive project closure contains 56 modules.
All 112 Lean/Markdown files were compared byte for byte with Library
`a9fae2951e0ea3e71a3319caba67d2b93350b350`; every pair matches.

The complete closure, with `Langlands.` suppressed, is:

```
Group.GL.Basic
Group.GL.BlockModulus
Group.GL.Blocks
Group.GL.Mirabolic
Group.GL.MirabolicRadical
Group.GL.Nonarchimedean
Group.GL.NonarchimedeanStatement
Group.GL.NormalizedCharacter
Group.GL.Padic
Group.GL.PadicBlocks
Group.GL.RankMaps
Group.GL.UpperUnipotent
HarmonicAnalysis.Basic
LocalField.Canonical
LocalField.Definitions
LocalField.Normalization.Definitions
LocalField.Normalization.Proof
LocalField.Normalization.Statement
LocalField.Topology
Representation.Category.Basic
Representation.Category.Twist
Representation.Derivative.Iteration
Representation.Derivative.MirabolicCharacter
Representation.Derivative.MirabolicMinus
Representation.Dual.Definitions
Representation.Jacquet.Coinvariants
Representation.Jacquet.Localization
Representation.Jacquet.PositiveCharacter
Representation.Jacquet.SmoothTwist
Representation.MatrixCoefficient.Definitions
Representation.MatrixCoefficient.LawsProof
Representation.MatrixCoefficient.LawsStatement
Representation.Shahidi.TwoBlocks
Representation.Smooth.Admissibility.CofinalProof
Representation.Smooth.Admissibility.CofinalStatement
Representation.Smooth.Definitions
Representation.Smooth.Transfer.PullbackProof
Representation.Smooth.Transfer.PullbackStatement
Representation.Smooth.Transfer.SubquotientProof
Representation.Smooth.Transfer.SubquotientStatement
Representation.Twist.AdmissibilityProof
Representation.Twist.AdmissibilityStatement
Representation.Twist.AlgebraProof
Representation.Twist.AlgebraStatement
Representation.Twist.ContinuousCharacterProof
Representation.Twist.ContinuousCharacterStatement
Representation.Twist.Definitions
Representation.Twist.RealPower
Representation.Twist.SmoothProof
Representation.Twist.SmoothStatement
Representation.Twist.SubquotientDefinitions
Representation.Twist.SubquotientProof
Representation.Twist.SubquotientStatement
Representation.Whittaker.Algebraic
Representation.Whittaker.GeneralLinear
Topology.Nonarchimedean.Subgroup
```

The mathematical dependencies, condition by condition, are just matrix
determinant formulas for the embedding identities; composition with the
actual normalized absolute value for determinant norms; elementary real
power, square-root and unit laws for scalar identities; and the published
one-step quotient, action, surjectivity and mapped-intertwiner laws for
the composite quotient maps and their formulas. The imported derivative
construction is used as a definition, not as a comparison theorem.
`Dual.Definitions` supplies elementary algebraic dual maps in the import
closure, not a duality result used here. No Whittaker uniqueness statement
is used as a proved input.

This proof route and its closure preserve the parent task's full positive
and socle exclusions: special-head product irreducibility,
`GenericSegmentProductUniqueness`, multisegment exhaustion, ordered
strong-head existence, quotient coverage, ordered conversion, tempered
uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable,
regular and socle exhaustion, analytic segment classification, forward
special-segment essential square-integrability, and every excluded
unlinked/linked socle-product, segment-socle product, juxtaposed
structure/quotient-Hom, adjacent or two-segment socle commutation, linked
socle gluing and ordered multisegment socle-existence conclusion are
absent. Their proof successors and downstream consequences supply no input.

The stronger shared tower restrictions are preserved as well. No input uses
`TwoSupercuspidalNonadjacentProductIrreducible`,
`TwoSupercuspidalProductStructure`, individual special-head/reverse-socle
or segment-socle/reverse-head existence, `SegmentFullJacquetFormula`,
`SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
`SegmentSpecialJacquetExponentNormFormula`, a segment derivative formula,
a segment-product criterion, or any analytic, square-integrability,
classification or exhaustion result. No unproved general derivative
comparison is assumed.

In particular this helper is independent of
`Langlands.Classification.SupercuspidalDerivatives` and proof task
`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`;
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement` and task
`62de5903-b616-4b5c-88eb-a066b77c5467`;
`Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` and parent
task `5ab445dc-d2b4-4072-80d1-6370870a4a26`; and
`LeviCuspidalCoinvariantFinitenessStatement` and proof task
`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`, including their successors and
downstream consumers. No mirabolic finite-length route from
`5428fe2c-013c-482d-aa6e-7df43e7191aa` is used. The closure contains none
of these conclusions or any segment or classification module.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Development compilation and
declaration inspection found no errors or warnings, independent `uF,uV`,
and only `propext`, `Classical.choice` and `Quot.sound`. This development
check is not independent mathematical acceptance or final exact-target
validation.
