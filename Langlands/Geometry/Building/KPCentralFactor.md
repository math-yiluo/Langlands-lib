# Actual central translations for the enlarged KP building

Author: Worker 455.

This definition unit constructs `Langlands.Geometry.Building.CentralFactor G`,
the actual additive dual `rationalCharacters G →+ ℝ`, as a dedicated type
synonym. The synonym carries its inherited real module structure and its own
actual `G(F)` translation action. `CentralFactor.dualEquiv` is the identity
real linear equivalence to that additive dual.

The field `F : Type u` has `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. Both characteristics and arbitrary
universe `u` are allowed. `G` is an actual group scheme over `Spec F`. The
central-factor construction needs no affineness or reductivity hypothesis.

## Source and conventions

The registered original is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The relevant passages, read directly, are §2.6(d), printed pp.102–103 / PDF
pp.133–134, and §4.3 opening and Lemma 4.3.1, printed p.178 / PDF p.209.
The authors' *Corrections and additions*, 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.25, remove the minus sign in the definition of the valuation
homomorphism. The translation in §4.3 still has a minus sign. Corrections
PDF pp.27–29 were checked and contain no §4.3 correction. No additional
source-specific errata note was found in the current public errata paths.

`CentralFactor.translation` is the negative of the already published actual
`rationalNormLogarithm G`, as a homomorphism into the multiplicative tag of
this additive space. The action is `g • v = v - H_G(g)`. `smul_apply` gives
its character coordinate as `v(χ) - ord_F(χ(g))`, using the actual
`rationalCharacterValuation` and `rationalNormLogarithm_eq_intValuation`.
No arbitrary character or valuation homomorphism is substituted.

## Intrinsic correctness and provenance

The homomorphism and action laws follow from additivity of the published
logarithm and the commutative additive group law. `translation_ker` uses
`rationalNormLogarithm_ker` and negation's zero criterion.
`smul_eq_self_iff` cancels the point coordinate and identifies its stabilizer
with that kernel. `stabilizer_eq` states the actual subgroup equality.
`actionKernel` is the actual pointwise fixer of the entire central factor;
`actionKernel_eq` identifies it with `rationalCommonNormKernel G` by testing
zero in one direction and fixing every point in the other.
`exists_fixed_iff` and `acts_trivially_iff` express Lemma 4.3.1(2)–(4).

The canonical dual is an internal realization of the source construction.
Its identification with the actual real cocharacter space of a split
component requires an explicit restriction-evaluation comparison in a separate
unit. This module proves no bounded-invariant-subset statement, topology,
compactness, derived-point annihilation, full-torus splitting, metric or
building existence result.
