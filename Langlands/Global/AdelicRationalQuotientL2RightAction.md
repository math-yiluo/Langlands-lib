# Right translation and compact averages on the full rational quotient

Let `F` be a number field and `G` an affine, locally finite type group scheme over `F` with `hG : IsConnectedReductive G`. Write `Q = G(F) \ G(𝔸_F)` and `μQ = rationalQuotientHaarMeasure F G`, the quotient of the ambient Haar measure by counting measure on the principal subgroup. These are the full quotient and measure used in the spectral transform. The construction does not divide out the positive split centre or restrict to the norm-one adelic group.

`rationalQuotientL2RightAction hG` is a monoid homomorphism from `G(𝔸_F)` to the continuous complex-linear endomorphisms of `L²(Q, μQ)`. For `y` in the group it takes `f` to the pullback by `x ↦ x y`. The unimodularity theorem `adelicHaarUnimodularity` supplies right invariance of ambient Haar, and `measurePreserving_rightTranslate_rationalQuotientHaarMeasure` passes it to the quotient. Thus `Lp.compMeasurePreservingₗᵢ` gives a norm-preserving map. The action law uses the fact that right translation by `y z` on points is translation by `y` followed by translation by `z`, so its pullback is the product of the operators in order `y, z`. The representative formula holds almost everywhere, with `x y` written as `LeftCosetSpace.mk Γ (x.out * y)` where `Γ` is the rational subgroup. This expression is independent of the representative because right multiplication descends to left cosets.

For joint continuity, the quotient translation is the continuous action of the opposite group on `Q`. Currying this continuous map and applying Mathlib's `Continuous.compMeasurePreservingLp` at exponent two proves continuity in both the adelic element and the `L²` class. The related `GroupSchemeQuotientL2Continuity` module uses the same continuity argument on the positive-centre quotient, not on this carrier.

For any compact subgroup `K`, let `dk` be `compactHaarProbability F G K hKc`. Given a complex weight `a` integrable for `dk`, `rationalQuotientL2CompactAverage` is the continuous linear operator obtained by the Bochner integral of `a k • R(k) f`. The orbit map on `K` is continuous, and `K` inherits second countability from the adelic group, so the orbit map is strongly measurable. `coeFn_rationalQuotientL2CompactAverage` applies the Library's `integratedTranslationPointwise` to the jointly measurable quotient action. It proves that for almost every `x` the integrand is integrable in `k`, and that the resulting function

\[
  x\longmapsto \int_K a(k) f(x k)\,dk
\]

represents the averaged `L²` class. No continuity of a representative of `f` is required.

## Provenance and scope

This is an internal construction on the Library's Haar quotient, supplying the target-side action for the covariance in J. Arthur, *An introduction to the trace formula* (2005), §7, especially pp. 34–35 (volume PDF pp. 46–47; `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`). The compact-average formula is a specialization of the Library's integrated translation theorem, not a claim that Arthur states that lemma in this form. The module does not construct the action on the inducing Hilbert spaces, commute integration with Eisenstein continuation, or identify these averages with wave packets. The approximation of right-translated symmetric packets required by `WavePacketTranslationStatement` remains separate.
