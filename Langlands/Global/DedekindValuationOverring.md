# Actual nontrivial valuation overrings of a Dedekind fraction-field model

This derived construction supplies the localization step needed for the actual
local integer factors in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Example 4.2, printed pages 9–10. It is a generic arithmetic
prerequisite, rather than a separately stated result in Conrad.

Let A be a Dedekind domain, K its original fraction field, and V a nontrivial
valuation subring of K containing the original A-image through a compatible
algebra. The given scalar tower states that its map into K is the original
fraction-field embedding. `center` is the actual contraction of V's maximal
ideal to A, and `prime` constructs the associated actual height-one prime.
`localizationEquiv` identifies the original localization of A at that prime,
inside K, with V as an A-algebra. It fixes the original field elements.
`isLocalization` transfers the actual localization structure to the original
V-algebra; no localization or center-nonzeroness conclusion is assumed.

To prove that the center is nonzero, suppose it were zero. Every nonzero
A-element would then map to a unit of V, with valuation one. Every K-element is
a fraction of two original A-elements, so it would belong to V. This would make
V the whole field, contrary to nontriviality. For the localization inclusion,
a permitted denominator is outside the center, hence maps to a unit of V. Its
valuation is one and every numerator has valuation at most one. The resulting
fraction belongs to V. The localization of a Dedekind domain at a nonzero prime
is a discrete valuation ring. The dimension-one valuation overring comparison
therefore makes this inclusion an equality, since V is not the whole field.
The original scalar tower proves that the resulting identity-on-elements ring
equivalence is an A-algebra equivalence.

The domain and fraction field inhabit independent arbitrary universes. No
Noetherianity, dimension or fraction-field premise beyond those in Dedekind and
fraction-field structures is added. There is no global-field, finite-constant,
finite-extension or separability assumption in this generic result. Its
arithmetic instantiations and completed-integer tensor and adelic point
comparisons remain obligations of the host task.

The center nonzeroness and localization inclusion proofs generalize the
corresponding `CurveModel` arguments in the published
`Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra`, ported from Anthropic's
Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, Copyright 2026 Anthropic, PBC, licensed
under Apache-2.0. The code header retains that attribution; the license and
project notices are at `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`. This generalization uses an arbitrary original Dedekind model,
its compatible scalar algebra into V, and its actual maximal-ideal contraction,
and adds the original A-algebra localization equivalence in independent
universes.
