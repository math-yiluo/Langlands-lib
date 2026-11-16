# Subgroup slices of a measurable fundamental domain

Author: Worker 306.

This internal measure lemma supports integration on the actual left
quotients used in global Rankin–Selberg integrals. Let `Γ ≤ U ≤ G`.
Suppose a measurable set `s ⊆ G` contains exactly one translate `γ g`
for each `g ∈ G`, with `γ ∈ Γ`. For `g ∈ G`, define its subgroup
slice to be

```text
{u ∈ U | u g ∈ s}.
```

The Lean definition is `subgroupSlice U s g`. Each slice is measurable.
The theorem `subgroupSlice_unique` transports the unique ambient
translator into `Γ.comap U.subtype`, using the inclusion `Γ ≤ U`.
The next theorem makes this an `IsFundamentalDomain` in `U`, for
any measure on `U`.

If `Γ.comap U.subtype` is countable and `ν` is left invariant on `U`,
`measure_subgroupSlice` compares this slice with any supplied
fundamental domain `t ⊆ U` and obtains `ν(slice) = ν(t)`. This uses
Mathlib's equality of the masses of fundamental domains; neither
finiteness nor positivity of that mass is assumed.

Finally, for an arbitrary nonnegative function `f` invariant under
left multiplication by `U`, `lintegral_subgroupSlice_indicator` proves

```text
∫_U 1_s(u g) f(u g) dν(u) = ν(t) f(g).
```

It identifies the integrand with the slice indicator times the
constant `f(g)` and uses the preceding mass equality. Measurability
of `f` is not needed for this particular constant-on-slice identity.

All content is derived from subgroup algebra, measurability of
multiplication, and the fundamental-domain API. The module does not
assert an Iwasawa decomposition, compute a conjugation modulus, or
prove an adelic Mellin estimate.
