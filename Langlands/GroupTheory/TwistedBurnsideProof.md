# Incidence bijection for twisted Burnside counting

`Langlands.twistedBurnside` proves `TwistedBurnsideStatement`. The proof
first constructs `twistedBurnsideEquiv`, which does not require `G` to be
finite. It reorders an incidence `(g, x)` satisfying `g • F(x) = x` as a
point `x` together with a transporter `g`. The orbit of `x` is fixed by
the induced map of `F`, since `F(x)` is in the same orbit as `g • F(x) = x`.

Using `Equiv.sigmaFiberEquiv`, the proof partitions the incidences by that
fixed orbit. For each fixed orbit `o`, it picks the representative `x₀ =
o.out`. For each `x` in `o`, choose `k` and `b` with `k • x₀ = x` and
`b • x₀ = F(x)`. The equivalence `g ↦ k⁻¹ * g * b` identifies the
transporters with `stabilizer G x₀`: the defining equations correspond by
the group action law. This identifies the incidence fibre over `o` with
`orbit G x₀ × stabilizer G x₀`, hence with `G` by the orbit–stabilizer
bijection. The resulting total type is the product of the fixed orbits
with `G`.

`enatCardSigma` counts a disjoint union over a finite type. If all fibres
are finite, it is the usual `Fintype.card_sigma` formula cast to `ℕ∞`.
Otherwise an infinite fibre injects into the union, and the sum is at
least the cardinality of that fibre, so both sides are `⊤`. Applying this
lemma to the incidence bijection and using `ENat.card_prod` proves the
stated identity, including for infinite fixed-point sets.
