# Arithmetic pair epsilon factors of direct sums

Author: Worker 1695.

This module proves, with no hypothesis beyond the axioms of a supplied
local-constant system, that arithmetic pair epsilon factors are multiplicative
on finite direct sums. Its main theorem
`Langlands.Correspondence.isArithmeticPairEpsilonFactor_directSum` is the body of
the premise `ArithmeticPairEpsilonDirectSum` of the conditional reduction
`Langlands.Correspondence.AssemblyEpsilonReduction`, written out in expanded
form. This module does not import that reduction module. On the way it proves the
published proposition `Langlands.LocalFactor.PairBlock.EpsilonDirectSum`
(Henniart 2002 §2.1, epsilon part). It also proves the two epsilon clauses of
`PairBlock.PairDistributivity` (§2.2) as separate theorems. The gamma clauses
of `PairDistributivity` are not proved here.

Throughout, `F : PadicField.{uF} p` with `[Fact p.Prime]`. `E` is an
intermediate field of the common closure, `Pair.{uF, uV} F E` is the
published type of common-closure pairs, and `(e, ε, hε)` is a supplied system
(`NonabelianSystem.IsSystem F e ε`).

## Part 1: binary sums of pairs (namespace `Langlands.LocalFactor.WeilDeligne`)

Here `A`, `B` are Weil–Deligne pairs over any field `K` and group `G`, with
carriers in possibly different universes. `I` is a normal subgroup of `G`.

- `sumFst`, `sumSnd`, `sumInl`, `sumInr`: the projections and inclusions of
  `A ⊕ B` as pair morphisms (they commute with the diagonal monodromy).
- `quotientSumEquiv I A B`: the published invariant quotient
  `V^I / (ker N)^I` of `A ⊕ B` (`quotientRepresentation`) is equivalent to the
  sum of the quotients of `A` and `B`. The forward map is
  `(quotientMap sumFst, quotientMap sumSnd)` and the inverse is
  `quotientMap sumInl + quotientMap sumInr`. Both identities are checked on
  representatives of the quotients.
- `conductorCorrection_sum`: the correction exponent is additive, because the
  rank of the quotient is (`Module.finrank_prod`).
- `quotientDeterminant_sum`: `det(-g | quotient)` of the sum is the product of
  the two determinants. Conjugate by `quotientSumEquiv` (`LinearMap.det_conj`)
  and use `LinearMap.det_prodMap`. The private lemma `det_neg_prodMap` gives the
  sign.
- `quotientCorrectionValue_sum`: the published quotient correction value
  `quotientCorrectionValue` is multiplicative on sums, by the two previous
  results.

## Part 2: the epsilon value of a sum (namespace `Langlands.LocalFactor.CommonClosureWeilDeligne`)

- `underlyingClass_sum`: the exact virtual class of `A ⊕ B` is the sum of the
  classes. This is `ExactGrothendieckGroup.ofRepresentation_shortExact`
  applied to the split sequence `0 → A → A ⊕ B → B → 0`.
- `conditionalDeligneValue_add`: Deligne's spectral value of the system is
  multiplicative on sums of virtual classes. This is the additivity clause
  `hε.2.1` of `IsSystem`.
- `quotientValue_sum`: the quotient correction factor of `A ⊕ B` is the
  product of the two factors.
- `conditionalEpsilonValue_sum`: the full conditional epsilon value is
  multiplicative on binary sums of continuous pairs. Unfold
  `conditionalEpsilonValue` and combine the three previous results.

`Langlands.LocalFactor.PairBlock.epsilonDirectSum F : PairBlock.EpsilonDirectSum F`
is `conditionalEpsilonValue_sum` with the arguments in the order of the
published statement.

## Part 3: direct sums of pairs (namespace `Langlands.WeilDeligneRepresentation`)

Here `directSum b` is the published direct sum of a finite family of pairs.

- `directSumSuccEquiv b`: `⊕_{i < n+1} b_i ≅ b_0 ⊕ ⊕_{i < n} b_(i+1)`. It is
  built from the linear equivalence `directSumSuccLinearEquiv`
  (`DirectSum.linearEquivFunOnFintype` and `Fin.consLinearEquiv`). It commutes
  with every componentwise endomorphism family (`directSumSuccLinearEquiv_comp_lmap`),
  so with the representation and with the monodromy.
- `directSumOneEquiv b`: `⊕_{i < 1} b_i ≅ b_0`. It is built the same way from
  `directSumOneLinearEquiv` and `directSumOneLinearEquiv_comp_lmap`.
- `tensorSumLeftEquiv A A' B : (A ⊕ A') ⊗ B ≅ (A ⊗ B) ⊕ (A' ⊗ B)` and
  `tensorSumRightEquiv B A A' : B ⊗ (A ⊕ A') ≅ (B ⊗ A) ⊕ (B ⊗ A')`. These are
  `TensorProduct.prodLeft` and `TensorProduct.prodRight`. The monodromy check is
  done on pure tensors.
- `directSumCongr e`: componentwise equivalences `A_i ≅ B_i`, whose
  carriers may lie in different universes, give `⊕ A_i ≅ ⊕ B_i`. The linear
  part is `DFinsupp.mapRange.linearEquiv`.
- `restrictDirectSumEquiv φ A`: restricting along `φ : H →* G` commutes with
  finite direct sums. The linear map is the identity.

## Part 4: finite products (namespace `Langlands.LocalFactor.CommonClosureGamma`)

- `directSum_isContinuous`: a direct sum of continuous pairs over `Fin (n + 1)`
  is continuous. The proof is by induction on `n`. It uses
  `directSumOneEquiv`, `directSumSuccEquiv`, the published binary result
  `PairBlock.sum_isContinuous` and invariance of continuity under equivalence
  (`FiniteRepresentation.isContinuous_iff_of_equiv`).
- `prod_of_directSum`: let `P` be a unit-valued invariant of continuous pairs
  that is invariant under equivalence and multiplicative on binary sums. Then
  `P(⊕_{i < n+1} b_i) = ∏_i P(b_i)`. The proof is by induction on `n`, using
  `directSumOneEquiv`, `directSumSuccEquiv` and `Fin.prod_univ_succ`.
- `conditionalPairEpsilonValue_sum_left` and
  `conditionalPairEpsilonValue_sum_right` are the two epsilon clauses of the
  published `PairBlock.PairDistributivity`. For example, the left clause is
  `ε((A ⊕ A') ⊗ B) = ε(A ⊗ B) ε(A' ⊗ B)` for the conditional pair epsilon value
  of the system. Transport along `tensorSumLeftEquiv` (or
  `tensorSumRightEquiv`) using `conditionalEpsilonValue_eq_of_equiv`, then apply
  `conditionalEpsilonValue_sum`.
- `conditionalPairEpsilonValue_directSum`: for families `a` over `Fin (n + 1)`
  and `b` over `Fin (m + 1)` of continuous pairs,
  `ε(⊕ a_i ⊗ ⊕ b_j) = ∏_i ∏_j ε(a_i ⊗ b_j)`. Apply `prod_of_directSum` twice:
  first in the left leg with `sum_left`, then in the right leg with
  `sum_right`. Equivalence invariance is
  `conditionalPairEpsilonValue_eq_of_equiv`.

## Part 5: the arithmetic factor (namespace `Langlands.Correspondence`)

- `IsBaseRestriction.nonempty_equiv`: suppose `classOf A = X` and `P` satisfies
  the published `IsBaseRestriction F X P`. Then the restriction of `A` to the
  bottom field is equivalent to `P`. The class equality gives an equivalence
  between `A` and the representative that `IsBaseRestriction` supplies
  (`classOf_eq_iff`). Restrict it (`restrictEquiv`) and compose.
- `restrict_equiv_directSum`: suppose `A ≅ ⊕_i B_i` for a finite family, and each
  `P_i` satisfies `IsBaseRestriction F (classOf B_i) P_i`. Then the bottom-field
  restriction of `A` is equivalent to `⊕_i P_i`. Compose the restricted
  `A ≅ ⊕ B_i`, `restrictDirectSumEquiv`, and `directSumCongr` of the
  equivalences from the previous lemma.
- `isArithmeticPairEpsilonFactor_directSum F eC ε hε ψ hr ht B B' A A' e hA hA' he`.
  The data are a nontrivial additive character `ψ`, natural numbers `r, t > 0`,
  families `B : Fin r → LocalWeilDeligneRepresentation.{uF, uP} F`, `B'` over
  `Fin t`, and representations `A`, `A'` with `⊕ B ≅ A` and `⊕ B' ≅ A'`. Assume
  that `e i j : ℂˣ × ℤ` satisfies
  `IsArithmeticPairEpsilonFactor F eC ε hε ψ (classOf (B i)) (classOf (B' j))`
  for all `i, j`. Then `RankinSelberg.epsilonFactorProduct e` satisfies
  `IsArithmeticPairEpsilonFactor` for `(classOf A, classOf A')`. The system
  `ε` has universe `uP`, the universe of the representations.

  Proof. Write `r = r' + 1` and `t = t' + 1`. The existence part of the factor
  for `(B i, B' 0)` supplies a continuous bottom-field datum `a_i` for each
  `B i`. The part for `(B 0, B' j)` supplies `a'_j` for each `B' j`. By
  `restrict_equiv_directSum`, `⊕ a` and `⊕ a'` are bottom-field restriction
  data of `classOf A` and `classOf A'`, with `A` and `A'` themselves as
  representatives. They are continuous by `directSum_isContinuous`. The base
  character, self-dual measure and geometric Frobenius come from the factor for
  `(B 0, B' 0)`. This gives the existence part of the conclusion.

  For the universal part, take any admissible datum `(ψ'', μ'', X, Y)`. By
  `IsBaseRestriction.nonempty_equiv`, `X ≅ ⊕ a` and `Y ≅ ⊕ a'`. The pair
  epsilon value is invariant under these equivalences. By
  `conditionalPairEpsilonValue_directSum` it equals `∏_i ∏_j ε(a_i ⊗ a'_j)`. The
  datum `(ψ'', μ'', a_i, a'_j)` is admissible for `(B i, B' j)`. So the
  universal part of the hypothesis on `e i j` evaluates each factor as
  `epsilonMonomial q (e i j).1 (e i j).2 s`.
  `RankinSelberg.epsilonMonomial_factorProduct` (with `1 < q` from
  `residueCardinality_gt_one`) identifies the double product with the monomial
  of `epsilonFactorProduct e`.

The conclusion is definitionally the conclusion of
`ArithmeticPairEpsilonDirectSum F eC ε hε` (module `AssemblyEpsilonReduction`)
at the same data. So `fun ψ _ _ hr ht B B' A A' e hA hA' he =>
isArithmeticPairEpsilonFactor_directSum F eC ε hε ψ hr ht B B' A A' e hA hA' he`
proves that premise for every system.

## Provenance

Derived. Henniart 2002 (*Une caractérisation de la correspondance de Langlands
locale pour GL(n)*), §2.1 states that `ε` multiplies on direct sums. §2.2
states that `ε` of `σ ⊗ σ'` for sums `σ = Σ σ_i` and `σ' = Σ σ'_j` is the
product over all `(i, j)`. Henniart cites Tate [Corvallis, §4] for both. The
published `PairBlock.EpsilonDirectSum` and `PairBlock.PairDistributivity`
(module `Langlands.LocalFactor.PairBlockStatement`) formalize these laws for
the measure-dependent values of an arbitrary supplied system. The proofs here
do not follow Tate. They use the definition of the conditional epsilon value
(Deligne's spectral value of the exact virtual class, times the quotient
correction on `V^I / (ker N)^I`): the additivity axiom of the system, and the
splitting of the invariant quotient of a direct sum. The finite-product and
correspondence-level statements are the n-ary consequence used by
Henniart §2.8 for direct sums of special blocks.

The componentwise `directSumCongr` equivalence is reused from
`Langlands.WeilDeligne.DirectSum`.
