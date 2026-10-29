# Descending interval block tensor scalar action and norm

This module proves the published statement
`Langlands.DescendingIntervalBlockScalarFormula` from
`Langlands.Representation.Exponents.DescendingIntervalBlockScalarStatement`.
The theorem `Langlands.descendingIntervalBlockScalarFormula` has the type
`DescendingIntervalBlockScalarFormula.{uF,uV} F T` for every p-adic field
`F : PadicField.{uF} p` and every `T : F.TopologicalData`. It is the proof unit
of task `821e5a8f-3731-41fb-a988-2a86568dbce5`. The route and most of the code
come from Worker 561's proof draft for statement task
`1b14e922-0259-49b6-a75b-142bb5ae5536`.

The module imports only the target statement module. Every lemma it uses about
the absolute value, the determinant-power character and the block tensor is
already imported by that statement.

## Notation

Let `B` be a block shape and let `σ i` be representations of
`GL_{B.size i}(F)`. Let `ω : Fˣ →* ℂˣ` be a character, let `r` and `m` be natural
numbers, and let `k i` be interval lengths with `∑ i, k i = m`. The prefix
`K i = ∑_{j < i} k j` is computed in `ℕ`. The block character is

`c i = ∏_{j < k i} ω · (|det|^(m - 1 - (K i + j)) on GL_r) ∘ scalar`.

Here the endpoint is a natural subtraction, cast to `ℝ`. The split-centre
character is `cB = ∏ i, (c i) ∘ (evaluation at i)`.

## Arithmetic helpers

`Classification.sum_descending_interval_real m K k` assumes `K + k ≤ m`. It
proves that the sum over `j : Fin k` of the cast of `m - 1 - (K + j)` equals
`k * ((2m - k - 1)/2 - K)` in `ℝ`. The proof is by induction on `k`. The case
`k = 0` is an empty sum, closed by `simp`. In the successor step,
`Fin.sum_univ_castSucc` splits off the last term `j = k`. The hypothesis
`K + (k + 1) ≤ m` gives `K + k ≤ m - 1` and `1 ≤ m`, so both natural
subtractions in that term cast to real subtractions (`Nat.cast_sub`). The
induction hypothesis, applied with `K + k ≤ m`, handles the other terms, and
`ring` finishes.

`Classification.prefix_add_le_sum k i` proves
`(∑_{j < i} k j) + k i ≤ ∑_j k j`. The index `i` does not lie in the filtered set
`{j | j < i}`, so the left side is the sum over that set with `i` inserted
(`Finset.sum_insert`). This set lies inside the whole index set, and the terms
are natural numbers, so `Finset.sum_le_sum_of_subset` gives the bound. With
`∑ i, k i = m`, every block therefore satisfies `K i + k i ≤ m`.

## The scalar action

`GeneralLinear.BlockShape.hasScalarCharacter_blockTensor_splitCentre` assumes
that each `σ i` has scalar character `c i` along `GeneralLinear.scalar`. It proves
that the actual block tensor `B.blockTensor σ` has scalar character
`∏ i, (c i).comp (Pi.evalMonoidHom _ i)` along `B.blockScalarLevi R`. This holds
for any commutative ring `R` and any characters `c i`.

The proof is by `PiTensorProduct.induction_on`. Take a scaled pure tensor
`r • ⨂ f i`. The published `B.blockTensor_tprod` says that the element
`B.blockScalarLevi R a` acts factorwise. In factor `i` it acts as
`σ i (scalar (a i))`, since the `i`-th component of `B.blockScalarLevi R a` is
`scalar (a i)` by definition. By hypothesis this is multiplication by `c i (a i)`.
Then `MultilinearMap.map_smul_univ` pulls the product of these scalars out of the
pure tensor. This product is the value of the product character at `a`
(`MonoidHom.finsetProd_apply`, `Units.coe_prod`), and the remaining identity
holds by `rfl`. For sums, both sides are additive. The tensor representation is
the published one; the proof does not choose any other representation.

## The norm

The shared lemma `T.norm_determinantPowerCharacter_scalar k s a` from
[SupercuspidalTwist](../Classification/SupercuspidalTwist.md) gives the norm
of `T.determinantPowerCharacter k s (scalar a)` as
`T.normalizedAbs a ^ (k * s)`. This reuses the published scalar-norm proof,
now placed with the character definition. The character is the real power
`s` of the determinant norm. Expanding `T.determinantNorm_scalar` gives
`(|a|^k)^s`; nonnegativity and `Real.rpow_natCast_mul` identify this with
`|a|^(k s)`, whose complex norm is itself.

`T.norm_prod_twistedScalarCharacter ω r k e a` evaluates the norm of the product
over `j : Fin k` of the characters `ω · (|det|^(e j) on GL_r) ∘ scalar` at `a`.
The complex norm is multiplicative (`norm_prod`, `norm_mul`). So the norm is the
product of `‖ω a‖` and `|a|^(r · e j)` over `j`. This product equals
`‖ω a‖^k · |a|^(r · ∑ j, e j)`, by `Finset.prod_mul_distrib`, `Finset.prod_const`
and `Real.rpow_sum_of_pos`. The last lemma uses `|a| > 0`. When `k = 0` both
sides are `1`.

`T.norm_prod_descendingIntervalScalarCharacter` specializes `e j` to the cast of
`m - 1 - (K + j)` under `K + k ≤ m`. It then substitutes the descending interval
sum, which gives `‖ω a‖^k · |a|^(r · k · ((2m - k - 1)/2 - K))`.

`T.norm_prod_blockDescendingIntervalScalarCharacter` evaluates `cB` at
`a : Fin b → Fˣ`. The product character evaluates to a product of values, and its
norm is the product of their norms. In block `i` the value is `c i (a i)`. The
previous lemma applies to it with `K = K i` and `k = k i`. The bound
`K i + k i ≤ m` comes from `prefix_add_le_sum` and `∑ i, k i = m`. This gives the
stated product formula, with the exponent computed in `ℝ`.

## The final theorem

`descendingIntervalBlockScalarFormula` introduces the data and the hypothesis
`∑ i, k i = m`, and unfolds the `let` bindings. It then introduces the
scalar-character hypotheses on the `σ i`. The first conjunct is
`hasScalarCharacter_blockTensor_splitCentre` with `R = F.Carrier`. The second
conjunct is `norm_prod_blockDescendingIntervalScalarCharacter` with `b = B.length`.

## Scope

The proof covers every block shape, every carrier universe `uV` and field
universe `uF`, and every character `ω`. It also covers `r = 0`, `m = 0`, zero
interval lengths and empty products. It adds no hypotheses such as `r > 0`,
`k i > 0` or `B.size i = r * k i`. The block sizes appear only through the
supplied scalar-character hypotheses. The proof does not assume
finite-dimensionality, finite length, admissibility, unitarity, smoothness or
nontrivial carriers. It uses only finite sums, multilinearity of tensor products,
and the published absolute value, determinant-power character and block tensor.
It uses no analytic, Jacquet-module, derivative or classification input. It
claims no Jacquet-module identification, no weak segment quotient formula and no
block-size divisibility.
