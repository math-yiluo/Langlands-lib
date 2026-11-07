# Componentwise maps of compact-open completions

Author: Worker 1775. Namespace: `Langlands.CompactCompletion`.

This is derived infrastructure for the completion in Renard 2026, I.1.4–I.1.5
(printed pp.9–10 / PDF pp.15–16) and its use in VI.9.7 (printed pp.205–206 /
PDF pp.211–212). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.1.5 defines the map on completions by applying a morphism to every
idempotent component. Here the components are indexed by compact open subgroups,
as in the published `CompactCompletion.completion`.

For a topological group `G`, smooth complex representations `ρ` on `V` and `σ`
on `W`, and a linear intertwiner `f : ρ.IntertwiningMap σ`, `map hρ hσ f` is
the linear map between their completions given by

`(map hρ hσ f v)_K = f(v_K)`.

The group and the two representation spaces have independent universes.
No local compactness or existence of compact open subgroups is assumed.
Naturality of the published normalized compact average,
`Compact.averageMap_commute`, proves compatibility of the image family.
Linearity is componentwise. `map_id` and `map_comp` prove the identity and
composition laws.

`map_translate` proves that applying `f` componentwise commutes with the
published family translation `(g · v)_K = ρ(g)v_{g⁻¹Kg}`. It follows directly
from the intertwining property. Consequently `mapFixed hρ hσ H f` is the
linear map from `completionFixed ρ hρ H` to `completionFixed σ hσ H`, for
every subgroup `H`, with the same component formula. Its identity and
composition laws are `mapFixed_id` and `mapFixed_comp`.

These are actual maps with proved intrinsic laws, rather than existence
statements. This module supplies the componentwise maps implicit in the
naturality clause of `LeviCompletionOppositeJacquetStatement`; it does not
construct its isomorphism, prove the generalized Jacquet lemma, or discharge
either VI.9.6 or VI.9.7.
