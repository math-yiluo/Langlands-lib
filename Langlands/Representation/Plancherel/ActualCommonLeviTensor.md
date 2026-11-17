# Actual common-Levi forward and inverse reverse-dual tensor

This is an internal adapter of the published actual common-Levi continuation
and positive-Levi coefficient constructions. Its source motivation is
Waldspurger (2003), V.3, formula (1), printed p.295 / PDF p.61, registered as
`waldspurger-2003-plancherel`. It constructs the formula for `s = 1` from
specified actual continued standard operators. It does not prove their
existence or the analytic assertions of V.3.1.

The field is an arbitrary nonarchimedean local field. The group is affine,
locally of finite type and connected reductive; the two cocharacters have
literally equal centralizer subgroup functors. The field universe and the
representation carrier universe are independent. The input compact open
subgroup has an explicit Iwasawa factorization for each of the two
parabolics. There is no characteristic, splitness, rank or induced
irreducibility restriction. The inducing object can be any smooth complex
representation for this algebraic construction.

`twistObject` uses the actual rational-character norm parameter algebra and
the published `parameterTransport` to the literal common Levi.
`dualTwistEquiv` identifies the smooth contragredient of that twist with the
inverse-parameter twist of the actual smooth contragredient. It retains each
underlying linear functional, as `dualTwistEquiv_apply` proves. Its linear
equivalence is the published `smoothContragredientTwistEquiv`; the
intertwining proof uses that the same parameter transport preserves
inversion. `dualInductionEquiv` lifts this equivalence through actual
positive-Levi induction using `CoefficientConjugation.leviInductionCongr`.

`ContinuedPair` packages explicit local analytic inputs: squared-modulus
compatibility, an open nonempty starting region, its inclusion in the
published `pairFullDomainRegion`, and a `PairContinuation` for precisely
that restricted actual compact standard family. The starting region may be
smaller than the full convergence domain. `ContinuedPair.operator` is the
published `continuedFamily`, not a freely supplied intertwiner.
`operator_compact` identifies it by the actual compact restriction and
extension maps with the supplied whole-operator numerator/denominator
presentation. `operator_agrees` identifies it with the original `pairFamily`
on its starting region, retaining that integral's source quotient measure.
Both facts are direct applications of the published continuation results.

Given a forward pair for `A` and a reverse pair for `A.contragredient`,
`regularLocus` is the intersection of the forward denominator locus with
the inverse image, under parameter inversion, of the reverse dual
denominator locus. `reverseDual` is the actual reverse continued operator
at the inverse parameter, transported on both ends through
`dualInductionEquiv`. `genericLocus` further requires bijectivity of the
particular forward and transported reverse dual operators. No nonemptiness
or density claim is contained in this definition.

`coefficientFiber` is the existing positive-Levi product-induced
coefficient object of the actual twist. `quotientCompact` proves compactness
of each parabolic quotient from the displayed compact representatives.
`tensorEquiv` supplies the published product induction equivalence with that
compactness discharged. `genericComparison` applies the published
`reverseDualTensorComparison` to the particular operators above. Thus it is
the forward standard continuation tensored with the inverse of that same
reverse dual continuation, transferred through the actual product
induction equivalences. The inverse is obtained from the supplied
bijectivity witness for that operator. It is not an independently chosen
coefficient equivalence.

The implemented laws specialize the published tensor laws:

- `genericComparison_tmul` gives the forward/inverse reverse-dual formula
  on pure tensors after the positive-Levi product induction comparison.
- `genericComparison_tmul_eval` evaluates it at any pair of actual rational
  points as the tensor of the two induced function values.
- `genericComparison_action` proves intertwining for the actual product
  rational-point action on every coefficient vector.
- `genericComparison_bijective` proves bijectivity on this generic locus
  from its two explicit operator bijectivity witnesses.

The construction uses value-preserving positive-Levi normalization and
makes no replacement of the compact probability coefficient map by a map
at a different Haar scale. In particular, it imposes no coefficient or
Hermitian-form preservation assumption and makes no such conclusion here.
It is compatible with using the compact probability maps and inverse-formal-
degree forms constructed in `LeviCompactCoefficients` on these same fibers.
Whole-operator rationality of the inverse tensor, nonempty and dense
generic loci, regular extension across individual factor poles at all
unitary parameters, and the coefficient and form identities remain
separate target obligations. This conditional construction alone is not a
closed unitary extension target.
