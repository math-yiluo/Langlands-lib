# Extending derivations to adic completions

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` extends an additive
map satisfying the Leibniz rule from a commutative ring `R` to its `I`-adic
completion `AdicCompletion I R`, for an arbitrary ideal `I`. All declarations
are in the namespace `Langlands.CommutativeAlgebra.FiniteTypeIntGRing`.

Throughout, `D : R →+ R` is an additive map and
`hD : ∀ a b, D (a * b) = a * D b + b * D a` is the Leibniz rule. Elements of
the completion are compatible families `x.val n ∈ R ⧸ (I ^ n • ⊤)`, and
`I ^ n • ⊤` is the ideal `I ^ n`.

## Statements

- `leibniz_mem_pow_of_mem_pow_succ I D hD n hx`: if `x ∈ I ^ (n + 1)` then
  `D x ∈ I ^ n`.
- `completionDerivAux I D x n`: the class modulo `I ^ n` of `D a`, where `a`
  is a chosen lift (`Quotient.out`) of the component `x.val (n + 1)`.
- `completionDerivAux_eq`: the same class is obtained from any lift `a` of
  `x.val (n + 1)`.
- `completionDeriv I D hD : AdicCompletion I R →+ AdicCompletion I R`: the
  additive map whose `n`-th component is `completionDerivAux I D x n`.
- `completionDeriv_val`: its `n`-th component is the class of `D a` for any
  lift `a` of the `(n + 1)`-st component.
- `completionDeriv_of a`: on the image `AdicCompletion.of I R a` of `a ∈ R`
  it is the image of `D a`.
- `completionDeriv_mul x y`: the extension satisfies the Leibniz rule
  `D̂ (x y) = x D̂ y + y D̂ x`.

The construction is internal to the project's proof and does not follow a
specific reference.

## Proofs

**Powers of `I`.** Induction on `n`. The case `n = 0` is trivial. For
`x ∈ I ^ (n + 2) = I ^ (n + 1) · I`, induct on membership in the product
(`Submodule.mul_induction_on`): for `a ∈ I ^ (n + 1)` and `b ∈ I`,
`D (a b) = a D b + b D a`, where `a D b ∈ I ^ (n + 1)` and
`b D a ∈ I ^ n · I = I ^ (n + 1)` by the induction hypothesis. Sums are
handled by additivity.

**Independence of the lift.** Two lifts of `x.val (n + 1)` differ by an
element of `I ^ (n + 1)`, and `D` maps their difference into `I ^ n`.

**The extension.** Compatibility of the components: for `m ≤ n`, a lift of
`x.val (n + 1)` is also a lift of `x.val (m + 1)` (the components of `x` are
compatible), so by independence of the lift the `m`-th component is the
image of the `n`-th one. Additivity and `D̂ 0 = 0` follow from independence
of the lift, using the sum of lifts as a lift of the sum and `0` as a lift
of `0`.

**Values.** `completionDeriv_val` is the independence of the lift.
`completionDeriv_of` uses `a` itself as a lift of every component of the
image of `a`.

**Leibniz rule.** Fix `n`, and let `a` and `b` be lifts of `x.val (n + 1)` and
`y.val (n + 1)`. Then `a b` lifts `(x y).val (n + 1)`, so the `n`-th
component of `D̂ (x y)` is the class of `D (a b) = a D b + b D a`. The classes
of `a` and `b` modulo `I ^ n` are `x.val n` and `y.val n`, so this class is
the `n`-th component of `x D̂ y + y D̂ x`.
