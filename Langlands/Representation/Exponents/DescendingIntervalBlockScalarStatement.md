# Descending interval block tensor scalars

This module states the proposition
`Langlands.DescendingIntervalBlockScalarFormula.{uF,uV} F T`. It is a
statement only: the pair defines a `Prop` and proves nothing. Publishing it
makes the assertion available as an exact proof target. A separate proof
must be checked and reviewed before anyone may use the formula as a theorem.

## Provenance

The proposition is internal algebra and finite-sum arithmetic. It is not
quoted from an original source. It is a helper for the derived norm
calculation for segment Jacquet modules of arbitrary block shape. There, an
ordered block tensor carries a descending run of determinant exponents
`m-1, m-2, …, 0`. The run is cut into consecutive intervals, and block `i`
gets the interval of length `k i`. This module isolates the scalar action of
the split centre on such a tensor and its norm. The statement is drafted from
Worker 561's unreviewed draft for this task.

## Data and hypotheses

Fix a prime `p`, a field `F : PadicField.{uF} p` and topological data
`T : F.TopologicalData`. The field universe `uF` and the carrier universe
`uV` are independent. The proposition quantifies over:

- a rank `n : ℕ` and an actual block shape `B : GeneralLinear.BlockShape n`;
- complex modules `V i : Type uV`, one for each block;
- actual representations
  `σ i : Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)`;
- any group homomorphism `ω : F.Carrierˣ →* ℂˣ`;
- natural numbers `r` and `m`;
- interval lengths `k : Fin B.length → ℕ` with `∑ i, k i = m`.

The prefix `K i = ∑ j < i, k j` is a sum of natural numbers. The block
character is the finite product

`c i = ∏ j : Fin (k i), ω * (T.determinantPowerCharacter r e).comp GeneralLinear.scalar`,

where `e` is the real cast of the natural number `m - 1 - (K i + j)`. Here
`T.determinantPowerCharacter r e` is the published character
`g ↦ |det g|^e` on `GL_r`. Composing with `GeneralLinear.scalar` evaluates
it on scalar matrices. The split-centre character is

`cB = ∏ i, (c i).comp (Pi.evalMonoidHom _ i)`,

so `cB a = ∏ i, c i (a i)` for `a : Fin B.length → F.Carrierˣ`.

## Assertion

Assume that each `σ i` has scalar character `c i` along
`GeneralLinear.scalar`. That is, `σ i (scalar t) v = c i t • v`. Then both
of the following hold:

1. The actual block tensor `B.blockTensor σ` has scalar character `cB` along
   the actual blockwise scalar map `B.blockScalarLevi F.Carrier`.
2. For every `a : Fin B.length → F.Carrierˣ`,

   `‖cB a‖ = ∏ i, ‖ω (a i)‖ ^ k i * T.normalizedAbs (a i) ^ x i`,

   with the real exponent `x i = r * k i * ((2*m - k i - 1)/2 - K i)`.

The endpoints `m - 1 - (K i + j)` in `c i` use natural subtraction. The
exponent `x i` is computed in the real numbers, with `K i` cast from `ℕ`.
The sum hypothesis gives `K i + k i ≤ m`. So when the interval is nonempty,
every natural endpoint equals the real number `m - 1 - K i - j`.

## Scope

The statement covers empty intervals, empty products, `r = 0`, `m = 0`, a
block shape with no blocks, and zero carriers. It requires no relation between
`B.size i` and `r * k i`. No smoothness or topology is assumed for the
representations. There is also no finite-dimensionality, finite length,
admissibility, unitarity, real-part witness or nontriviality assumption.

The proposition claims no identification of a Jacquet module. It gives no
formula for a weak segment quotient and no block-size divisibility. It uses
the published block tensor and determinant-power characters themselves, not
substitutes for them.

## Intended proof

This section is a plan, not a proof. On pure tensors, `B.blockTensor_tprod`
together with the scalar action on each factor and multilinearity pulls out
`∏ i, c i (a i)`. Tensor induction then covers every vector. For the norm,
multiplicativity of the complex norm and `|det (t I_r)|^e = |t|^(r e)`
reduce the problem to the sum of the exponents. The descending interval sum is

`∑ j < k, (m - 1 - K - j) = k * ((2*m - k - 1)/2 - K)`.

These steps use elementary linear algebra and finite sums. No analytic
input is needed.
