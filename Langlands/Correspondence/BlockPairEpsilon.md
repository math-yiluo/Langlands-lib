# Arithmetic epsilon factors of pairs of special blocks

Author: Worker 1695.

This module computes the conditional epsilon value of a pair of uncentered
special blocks on the Galois side. It is a step toward deriving the
epsilon compatibility of segment pairs from the published, unproved statements
`LocalFactor.PairBlock.BlockPairGamma`,
`RankinSelberg.SegmentHeadFactorStatement` and the Euler block statements.
It proves two things:

1. For every supplied system, the epsilon value of the pair
   `(ρ ⊗ S_(n+1), ρ' ⊗ S_(m+1))` equals the double product of the epsilon
   values of the twisted factors `ν^(i+j) (ρ ⊗ ρ')`, `i ≤ n`, `j ≤ m`, times the
   quotient correction of the block tensor. The quotient correction is a nonzero
   constant times a power of `q_E^(-s)`. This needs no hypothesis beyond the
   system axioms.
2. Assuming the published block-pair gamma law `PairBlock.BlockPairGamma F`
   (Henniart 2002 §2.4), the quotient correction times the L-ratio of the
   block tensor is the product of the L-ratios of the twisted factors, at every
   common regular point.

Throughout, `F : PadicField.{uF} p` with `[Fact p.Prime]`. `E` is an
intermediate field of the common closure, `ν = (normCharacter F E).toMonoidHom`,
`(e, ε, hε)` is a supplied system (`NonabelianSystem.IsSystem F e ε`), `ψ` and
`μ` are an additive character and a Haar measure, and `Φ` is a geometric
Frobenius. `block ν A m` is the published uncentered block `A ⊗ S_m`, with
carrier `A ⊗ (Fin m → K)`. `twistedFactor F E ρ k` is the published
zero-monodromy pair `ν^k ⊗ ρ`.

## Part 1: Weil–Deligne helpers (namespace `Langlands.WeilDeligneRepresentation`)

- `blockRepresentationEquiv ν A m`: the Weil action of `block ν A m` is
  equivalent to the direct sum of the twists `ν^i A`, `i < m`. The linear map is
  `TensorProduct.piScalarRight` followed by the inverse of
  `DirectSum.linearEquivFunOnFintype`. It intertwines because the special block
  acts on coordinate `j` by the scalar `ν(g)^j` (`Special.action`). Monodromy is
  not preserved, so this is only an equivalence of the Weil actions.
- `zeroMonodromyEquivOfEquiv`: if two pairs both have zero monodromy, every
  equivalence of their Weil actions is an equivalence of pairs.
- `directSum_zeroMonodromy_monodromy`: a direct sum of zero-monodromy pairs has
  zero monodromy.
- `tensor_monodromy_eq_zero`: the tensor of two pairs with zero monodromy has
  zero monodromy (`N ⊗ 1 + 1 ⊗ N'`).

## Part 2: twists of tensors (namespace `Langlands.FiniteRepresentation`)

- `tensorTwistEquiv χ η A B`: `χ A ⊗ η B` is equivalent to `(χ η)(A ⊗ B)`
  through the identity linear map. On pure tensors this is
  `(χ(g) a) ⊗ (η(g) b) = (χ(g) η(g)) (a ⊗ b)`.
- `twistEquivOfEq`: twists by equal characters are equivalent through the
  identity map.

## Part 3: epsilon of block pairs (namespace `Langlands.LocalFactor.CommonClosureGamma`)

- `twistedFactor_eq_zeroMonodromy`: `twistedFactor F E ρ k` equals the
  zero-monodromy pair of the twist by `ν ^ k`, with the power taken in the monoid
  of homomorphisms. The published definition takes the power of the continuous
  homomorphism and then forgets continuity. The two expressions agree pointwise
  but are not definitionally equal.
- `blockZeroMonodromyEquiv E ρ n`: the zero-monodromy pair on the Weil action of
  `block ν ρ n` is equivalent to `⊕_{i<n} twistedFactor F E ρ i`. This is
  `blockRepresentationEquiv` combined with `zeroMonodromyEquivOfEquiv`.
- `conditionalPairEpsilonValue_block` (GA1): for continuous `ρ`, `ρ'`, all
  `n`, `m` and all `s : ℂ`,

  `ε(block ρ (n+1), block ρ' (m+1))(s) =
     (∏_{i ≤ n} ∏_{j ≤ m} ε(twistedFactor ρ i, twistedFactor ρ' j)(s)) ·
     quotientValue(block ρ (n+1) ⊗ block ρ' (m+1))(s)`.

  Proof: `conditionalEpsilonValue` is the Deligne value of the underlying
  virtual class times `quotientValue`. The underlying class of the block tensor
  is the underlying class of the tensor of the two zero-monodromy pairs on the
  Weil actions. The published `conditionalEpsilonValue_of_monodromy_zero` then
  identifies the Deligne value with the pair epsilon value of those
  zero-monodromy pairs. `conditionalPairEpsilonValue_eq_of_equiv` moves it along
  `blockZeroMonodromyEquiv` on both sides. Finally
  `conditionalPairEpsilonValue_directSum` (module
  `Langlands.Correspondence.ArithmeticEpsilonDirectSum`) splits the double
  direct sum.
- `quotientValue_eq_monomial` (GA2): `quotientValue F E A Φ s` equals the
  constant `WeilDeligne.quotientConstantCorrection A (inertia F E) Φ.val`
  times `spectralParameter q_E s ^ conductorCorrection A (inertia F E)`. This
  holds by definition (`rfl`).
- `twistedPairEquiv E ρ ρ' i j` (GA3): the tensor of `twistedFactor ρ i` and
  `twistedFactor ρ' j` is equivalent to `twistedFactor (ρ ⊗ ρ') (i + j)`. It
  uses `tensorTwistEquiv`, then `twistEquivOfEq` for `ν^i ν^j = ν^(i+j)`, then
  `zeroMonodromyEquivOfEquiv`.
- `conditionalPairEpsilonValue_twistedFactor`: the pair epsilon value of
  `(twistedFactor ρ i, twistedFactor ρ' j)` equals the epsilon value of
  `twistedFactor (ρ ⊗ ρ') (i + j)`. This is `conditionalEpsilonValue_eq_of_equiv`
  along `twistedPairEquiv`.
- `quotientValue_mul_lRatioValue_block` (GB): assume
  `hBPG : PairBlock.BlockPairGamma.{uF, uP} F`. Let `T` be the tensor of the
  blocks. Let `s` be a regular point for `T` and `Φ`, and let
  `t i j` be regular points for `twistedFactor (ρ ⊗ ρ') (i + j)` with
  `(t i j).val = s.val`. Then

  `quotientValue(T)(s) · lRatioValue(T)(s) = ∏_{i ≤ n} ∏_{j ≤ m} lRatioValue(twistedFactor (ρ ⊗ ρ') (i+j))(t i j)`.

  Proof: `hBPG` gives `γ(T)(s) = ∏∏ γ_(i+j)(t i j)`. Rewrite the left side with
  the published `conditionalPairGammaValue_eq` (gamma = epsilon · L-ratio) and
  GA1. Rewrite each factor on the right with `conditionalGammaValue` and
  `conditionalPairEpsilonValue_twistedFactor`, then distribute the products
  (`Finset.prod_mul_distrib`). The common factor `∏∏ ε_pair` is a unit, and
  cancelling it (`mul_left_cancel` in `ℂˣ`) gives the identity.

## Provenance and scope

Derived. Henniart 2002 (henniart-2002-characterization) §2.3–§2.4 describes
the factors of a special block `ρ ⊗ Sp(n)` through its twisted constituents
`ν^i ρ`, and states the gamma law for pairs of blocks that is formalized as the
published `PairBlock.BlockPairGamma`. GA1–GA3 are proved here directly from the
published definitions of the conditional epsilon value and of the block, and
need only the system axioms. GB is a direct algebraic consequence of the published
statement `BlockPairGamma`, which it takes as the hypothesis `hBPG`. The module
does not prove `BlockPairGamma` and asserts no new literature claim.

This module imports `Langlands.Correspondence.ArithmeticEpsilonDirectSum` for
`conditionalPairEpsilonValue_directSum` and `directSum_isContinuous`.
