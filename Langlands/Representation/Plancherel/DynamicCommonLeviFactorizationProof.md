# Ordered factorization of distance-additive dynamic radicals

`distanceAdditiveRadicalFactorization` proves `DistanceAdditiveRadicalFactorizationStatement`.
It obtains the smoothness instance from `IsConnectedReductive` and wraps the
published `distanceAdditiveRadicalFactorizationData` in `Nonempty`. The data
give the three ordered multiplication homeomorphisms for the rational points
of the dynamic radicals. This is a structural input to the common-Levi
composition of standard intertwining integrals. [Published statement](DynamicCommonLeviComposition.md)

Write `Uᵢ` and `Ūᵢ` for the radical and opposite radical of `ψᵢ`, and put
`V = U₁ ∩ Ū₀` and `W = U₂ ∩ Ū₁`. To prove `V ≤ U₂`, the construction writes
`x ∈ V` as `c d` in the product chart on `Ū₀`, where `c ∈ U₂ ∩ Ū₀` and
`d ∈ Ū₂ ∩ Ū₀`. At a contracting unit `t`, the value `ψ₁(t)` belongs to the
common Levi, so its powers preserve the chart factors by conjugation.
The conjugates of `x` tend to the identity since `x ∈ U₁`. Continuity of the
second coordinate implies the same convergence for the conjugates of `d`,
so the dynamic contraction criterion gives `d ∈ U₁`. The opposite
inclusion `Ū₀ ∩ Ū₂ ≤ Ū₁` gives `d ∈ Ū₁`, hence `d = 1` and `x = c ∈ U₂`.

The common-Levi charts identify `(U₀ ∩ U₁) × V` with `U₁` and
`(U₁ ∩ U₂) × W` with `U₂` by multiplication. Since `V ≤ U₂`, a product
in the first chart belongs to `U₂` exactly when its first factor does.
Using `U₀ ∩ U₂ ≤ U₁`, the construction therefore restricts the first chart
to `(U₀ ∩ U₂) × V ≃ₜ U₁ ∩ U₂`. Composing with the second chart gives the
homeomorphism `(U₀ ∩ U₂) × (V × W) ≃ₜ U₂` by ordered multiplication.
[Published chart construction](DynamicCommonLeviOrderedRadicals.md)
