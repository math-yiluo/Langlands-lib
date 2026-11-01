# Proof of additivity of actual cohomological Euler characteristics

`DerivedSections.eulerCharacteristicAdditivity` proves the complete
`EulerCharacteristicAdditivityStatement` with its field and universe parameters
unchanged.

The functor used is the given morphism's actual `relativeGlobalSections f`.
The published `DerivedPlus.rightDerived_exact₂`, `rightDerived_exact₃`, and
`rightDerived_exact₁` give the three kinds of consecutive exact segments in its
long exact sequence for `S`. Exactness in `ModuleCat K` identifies each incoming
linear-map range with the outgoing kernel. Rank-nullity therefore gives the
dimension of each middle vector space as the sum of its incoming and outgoing
range dimensions.

Write `aₙ`, `bₙ`, and `cₙ` for the integer dimensions of the actual cohomology
objects of `S.X₁`, `S.X₂`, and `S.X₃`, and `rₙ` for the dimension of the range
of the map on degree-`n` cohomology induced by `S.f`. Adding the rank-nullity
identities at `Hⁿ(S.X₂)` and `Hⁿ⁺¹(S.X₁)` and subtracting the identity at
`Hⁿ(S.X₃)` gives
`bₙ + aₙ₊₁ = rₙ + cₙ + rₙ₊₁`.
The actual cohomology map induced by `S.f` is injective in degree zero, by
`DerivedPlus.mono_rightDerived_zero_map`, so `r₀ = a₀`.

An induction using this recurrence proves
`Σₙ<N (-1)ⁿ (bₙ-aₙ-cₙ) = (-1)ᴺ (aᴺ-rᴺ)`.
Choose `N` to be the maximum of the three cohomological vanishing bounds.
The domain of the degree-`N` map is zero, so both `aᴺ` and `rᴺ` vanish.
Outside this bound every Euler summand vanishes. Converting the three published
Euler characteristic definitions to finite sums and rearranging the resulting
zero sum proves the assertion.

The proof uses neither coherence nor properness beyond the explicit
`HasFiniteCohomology` hypotheses. It adds no assumptions on characteristic,
connectedness, or nonemptiness, and computes no polarized degree.
