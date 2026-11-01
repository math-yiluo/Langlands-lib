# Higher derivatives of left mixed products

Author: Worker 1190.

This internal helper supplies the positive-rank induction and the all-rank
isomorphism conjunct of `LeftMixedProductDerivative`, with
`hPhi : MirabolicProductMinus.LeftPhiCompatibility.{uF,uV} F T` explicit.
It is part of the proof package in
[`LeftMixedProductDerivativeProof`](LeftMixedProductDerivativeProof.md),
which discharges that argument with the independently accepted and published
`MirabolicProductMinus.leftPhiCompatibility T`. This helper does not prove
that clause or the final unconditional conjunction.

`derivativeOfOrderTargetTransport` converts the source-rank wrapper of order
`j + 1` on `P_(N+1)` to `mirabolicDerivative n j` after an explicit source cast
`N = n + j`. It eliminates independent equalities for the target rank and
number of Phi steps, so the remaining output cast is reflexive. It uses no
Phi compatibility premise.

`leftPhiStepIso` postcomposes the stated positive left Phi comparison with
the inverse of the output rank cast `(k + 1) + r = k + (r + 1)`. On the
source, `phiMinus_rankCast` and `mirabolicRankCast_trans` move this inverse
cast before Phi. On the target, `mirabolicRankCast_symm_comp` cancels the
two casts. This gives a step with output rank `(k + 1) + r`.

`leftMixedDerivativeIterateIso` inducts on `j` with second-factor target
rank `n`. At `j = 0` it uses the independently accepted and published
`MirabolicProductMinus.leftPsiCompatibility`. At `j + 1`, the largest-rank
Phi is applied first by `mirabolicDerivative_succ`; the source cast
commutes with it using `phiMinus_rankCast`. The conditional
`leftPhiStepIso` moves this Phi to the second input. Whiskering the
induction hypothesis then compares the remaining derivative, and
`prodCompProdIso` together with the identity unitor combines the two input
functors. Explicit associators keep elaboration finite.

`leftMixedDerivativeOfOrderIso` is the exact positive GL rank formula from
the first conjunct, still with the explicit Phi premise. For `i = j + 1`,
put `n = r + 1 - i` and cast the second input along `r = n + j`.
`leftMixedProduct_rankCast` moves this cast through the mixed product.
`derivativeOfOrderTargetTransport` identifies both source-rank wrappers
with the target-rank derivatives. Whiskering the preceding induction
isomorphism and combining product functors yields the displayed comparison.
The case `i = 0` contradicts the valid-order premise; the top order
`i = r + 1` is included with `n = 0`.

All comparisons are isomorphisms of actual functors on the full input product
category. Their components and inverses are compositions of the supplied
comparison components, equality isomorphisms, whiskered isomorphisms and
categorical associators/unitors. Naturality therefore includes both input
maps. The independent field and carrier universes are retained. This helper
does not establish the Phi comparison, vanishing, or the complete
target proposition. Its premise must not be hidden or discharged by a citation,
statement, draft, pending artifact, or consumer conclusion.

`leftMixedProductDerivativeIso` assembles all GL ranks of the first conjunct.
It splits on the GL rank: zero uses the published arbitrary-carrier
`leftMixedProductZeroRankIso`, and a successor uses the conditional
`leftMixedDerivativeOfOrderIso` above. It wraps each isomorphism in `Nonempty`.
The theorem explicitly retains `hPhi : LeftPhiCompatibility F T`; it is not
the no-premise theorem required by the task.

Where this helper applies `Classical.choice` to a compatibility proposition,
the resulting isomorphism is some data of the asserted type. No component
equation identifies it with a witness used to prove that proposition.
Descriptions of the later composites refer to the selected isomorphisms.


The literature scope is Bernstein–Zelevinsky (1977), Corollary 4.14(a),
printed p.458 (PDF p.19), derived there from 4.13(b). The registered original
is `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The target-rank induction, equality elimination and categorical packaging
are internal derived content. All other actual mathematical inputs are
published: `OrderRecursion`, `MixedProductRankCast`,
`MirabolicProductMinusLeftPsi`, and `LeftMixedProductZeroRank`; the target
statement supplies only types. No unpublished assertion supplies a proof.
The entry proof's Markdown records the complete combined import closure,
unchanged imported-pair checks and both full condition-by-condition exclusion
audits for this helper and its dependencies. The Phi argument is explicit
here and is discharged there only by the verified published clause.
