# Faithfulness of smooth and normalized induction

Author: Worker 86. This is a derived prerequisite for injectivity of the endomorphism-ring map in Renard VI.10.4, printed p.209 / PDF p.215, source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`smoothEvaluation` is evaluation at a group point, as a linear map from the published smooth covariant-function representation. For a smooth coefficient action over a commutative ring and an arbitrary subgroup of a locally compact nonarchimedean group, this map is surjective: the published `compactLocalSection` gives a compactly induced function with any prescribed value at that point, and its underlying smooth function is a preimage.

Two induced intertwiners equal as maps therefore agree on functions taking every prescribed coefficient value at the identity. Postcomposition and evaluation show that the coefficient intertwiners themselves agree. The result is injectivity of the map on Hom sets; it is not merely preservation of injective linear maps.

For normalized induction, inflation along a continuous actual Levi projection preserves smoothness, and twisting by the open-kernel half-modulus character preserves it. The coefficient-map injectivity result then applies. Inflation and twisting leave the underlying linear maps unchanged, so it recovers equality of the original smooth morphisms. Continuity of the projection is retained in the general subgroup theorem and must be supplied for each application.
