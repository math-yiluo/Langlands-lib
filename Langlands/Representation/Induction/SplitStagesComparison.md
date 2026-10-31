# Compact split stages comparison

This internal construction composes compact induction in stages, normal
coinvariants for a split quotient, and the actual relative kernel integral.
It is an unnormalized prerequisite for the p-adic orbit comparison. It does
not assert the parent normalized functor isomorphism.

## Data and actual groups

Let `G` be a locally compact Hausdorff topological group and `L` a topological
group. Let `r : G →* L` and `s : L →* G` be continuous with `r(s(l)) = l`.
Let `H ≤ P ≤ G` be closed, with `ker r ≤ P`, and suppose `s(l) ∈ H` for
every `l ∈ P.comap s`. The coefficient representation `σ` of `H` is an
arbitrary smooth complex representation; no topology, dimension or length
condition is imposed on its module. The group and coefficient universes are
independent, including a separate target coefficient universe for naturality.

Put `K = P.comap s` and `HP = H.subgroupOf P`. The coefficient `σP` is
`σ` pulled back through the actual equivalence `HP ≃* H` induced by `H ≤ P`.
The imported map `splitStagesRetraction : P →* K` from
`SplitStagesRetraction` sends `p` to `r(p)`. Its codomain
membership comes from `splitQuotient_section_mem`; its section is
`s.subgroupComap P`. Its actual kernel is proved equal to
`r.ker.subgroupOf P`. Both maps have the induced subgroup topologies and are
continuous by restriction. The inner inducing intersection is
`I = HP.comap (splitStagesRetraction ...).ker.subtype`.

The comparison takes a compact-open subgroup neighborhood basis for `G` and
one for the restricted kernel. It also takes Borel structures and local
compactness for that kernel, Borel structures for `I` and its left quotient,
left and right invariant regular Haar measures on the kernel and `I`, and a
compatible quotient measure `ν` finite on compact sets. Local compactness of
`P` and of `I` is derived from closedness where needed. Closedness of the
ambient kernel is supplied explicitly. These are the hypotheses of the
imported actual quotient-integral and normal-coinvariant constructions; the
construction assumes no comparison map or bijectivity premise.

## Transport and composition

`normalCoinvariantsEquiv` descends an ambient representation equivalence and
its inverse using the actual `normalCoinvariantsMap`. Induction on quotient
representatives proves both inverse laws. `normalCoinvariantsCongr`
transports the actual quotient representation along an equality of normal
subgroups. `restrictAlongEquiv` retains the linear equivalence and restricts
its intertwining law. `compactInducedEquiv` applies the published coefficient
postcomposition maps for an equivalence and its inverse; evaluation proves
the inverse laws.

`splitStagesInnerEquiv` first identifies `r.ker.subgroupOf P` with the kernel
of the restricted retraction, then uses `splitKernelCompactEquivariantEquiv`.
Its coefficient representation is precisely

`κ = twist χ (splitKernelCoefficientAction rP sP HP hsH σP)`,

where `χ` is the complex character of `splitKernelHaarRatio rP sP HP hsH`.
That positive character is the actual subgroup-to-kernel Haar ratio for
inverse conjugation by the section. It is retained in this unnormalized
comparison. `splitStagesInnerIntegral` names its actual integral before
descent and derives local compactness of `P` from closedness.

`splitStagesCompactEquiv` gives an `L`-representation equivalence from
`((compactInduced H σ).toCoinvariants r.ker).comp s` to
`compactInduced K κ`. Its forward map is the composition of the inverse of
compact induction in stages, actual ambient normal coinvariants, the
published `normalSplitCompactEquiv`, and compact induction of the inner
relative integral. Each component is a bundled representation equivalence.

## Representative formula and naturality

`splitStagesSlice` is the actual inner compact function obtained from the
inverse stages map. Its value at `q : P`, with outer point `x : G`, is
`f(q*x)`. `splitStagesKernelSlice` restricts this compact function to the
actual restricted kernel, at outer point `s(l)`. Its value at `n` is exactly
`f(n*s(l))`, with the subgroup inclusions understood.

The representative evaluation theorem states that the composite sends
`[f]`, evaluated at `l`, to the relative integral of this slice.
`splitStagesCompactEquiv_eval_mk_integral` writes that value as the actual
`AlgebraicIntegral.integral ν` of the published finite-image simple
function. `splitStagesIntegrand_mk` identifies its value at a quotient
representative `n` with the actual coefficient class `[f(n*s(l))]` in
`Representation.Coinvariants (σP.comp (rP.ker.subtype.subgroupComap HP))`.
There is no additional scalar in this integral formula; the Haar ratio
appears in its equivariance through `κ`.

`splitStagesCoefficientMap` is the actual intersection-coinvariant map
induced by a coefficient intertwiner, bundled as an intertwiner of the
Haar-twisted coefficient actions. The slice commutes with coefficient
postcomposition pointwise, and the raw inner integral commutes with this
quotient map by the imported integral naturality theorem. Quotient induction
and the representative evaluation formula then prove
`splitStagesCompactEquiv_natural` for every smooth coefficient intertwiner in
independent coefficient universes. The source map is the actual map on
ambient kernel coinvariants of `compactInducedMap H T`; the target map is
`compactInducedMap K` of `splitStagesCoefficientMap`.

## Provenance and remaining application

These declarations are internal compositions of the named imported
constructions; they do not claim a new theorem verbatim from literature.
They organize the restriction, stages and relative integral needed in the
local comparison of Bernstein–Zelevinsky (1977), sections 5.4–5.17. The
p-adic application still requires the actual parabolic subgroup
identifications, identification of the inner quotient with refined source
Jacquet, comparison with the target refined induction, and cancellation of
the normalization characters as in section 6.4. None of these remaining
steps is asserted here.
