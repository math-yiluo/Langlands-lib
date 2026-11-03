# Finite-rank trace on short exact sequences

Authors: Worker 34 (Lean proof and first draft) and Worker 969 (Markdown
revision and submission).

This module proves three derived linear algebra lemmas about the genuine
finite-rank trace `Langlands.FiniteRankEnd.trace` of
`Langlands.LinearAlgebra.FiniteRankTrace`. The carriers `A : Type uA`,
`B : Type uB` and `C : Type uC` are arbitrary complex vector spaces in three
independent universes. None of them is assumed finite-dimensional or carries a
topology. The lemmas support short-exact additivity of actual distribution
characters, `Langlands.Character.distributionShortExactAdditivity`. They are
standard linear algebra and are not attributed to a particular source.

## Cyclicity through a finite-dimensional range

`trace_comp_of_hasNoetherianRange f hf g` takes `f : A →ₗ[ℂ] B` with Noetherian
range, `hf : f.HasNoetherianRange`, and any `g : B →ₗ[ℂ] A`. It proves

```
trace ⟨g.comp f, hf.comp_left g⟩ = trace ⟨f.comp g, hf.comp_right g⟩
```

in `finiteRankEnd A` and `finiteRankEnd B` respectively. Mathlib's
`HasNoetherianRange.comp_left` and `comp_right` supply the two membership
proofs. Over `ℂ` the Noetherian range `f.range` is finite-dimensional. The proof
applies `FiniteRankEnd.trace_eq_of_factorization` twice through `f.range`:
`g ∘ f` factors as `(g ∘ subtype) ∘ f.rangeRestrict`, and `f ∘ g` factors as
`subtype ∘ (f.rangeRestrict ∘ g)`. Both traces become the trace of the same
endomorphism `f.rangeRestrict ∘ g ∘ subtype` of `f.range`, which closes the goal
by `rfl`.

## Linear splittings of an exact sequence

`exists_splittings_of_exact f g hf hg hfg` takes linear maps
`f : A →ₗ[ℂ] B` and `g : B →ₗ[ℂ] C` with `f` injective, `g` surjective and
`f.range = g.ker`. It produces linear maps `p : B →ₗ[ℂ] A` and
`s : C →ₗ[ℂ] B` with

```
p.comp f = id,  g.comp s = id,  f.comp p + s.comp g = id.
```

The proof chooses a left inverse `p₀` of `f` with Mathlib's
`LinearMap.exists_leftInverse_of_injective` for vector spaces. It chooses a
right inverse `s` of `g` with `LinearMap.exists_rightInverse_of_surjective`,
which applies because a complex vector space is free, hence projective. It then
sets `p = p₀ ∘ (id - s ∘ g)`. Since `g ∘ f = 0`, `p ∘ f = p₀ ∘ f = id`. For
`b : B`, the vector `b - s (g b)` lies in `g.ker = f.range`, say it is `f a`.
Then `f (p b) = f (p₀ (f a)) = f a = b - s (g b)`, which gives the third
identity. The splittings are only linear; no group action or equivariance
appears in this lemma.

## Additivity of the trace

`trace_shortExact` takes the same exact data `f`, `g`, `hf`, `hg`, `hfg`,
finite-rank endomorphisms `TA`, `TB`, `TC` of `A`, `B`, `C`, and the commuting
identities

```
hfT : TB.val.comp f = f.comp TA.val
hgT : g.comp TB.val = TC.val.comp g
```

It proves `trace TB = trace TA + trace TC`. The proof takes splittings from
`exists_splittings_of_exact`. The third splitting identity writes
`TB = SA + SC` with `SA = f ∘ (p ∘ TB)` and `SC = s ∘ (g ∘ TB)`. Both summands
have finite rank because `TB` does. Linearity of `trace` splits the sum. For
`SA`, cyclicity with the finite-rank map `p ∘ TB` gives
`trace SA = trace (p ∘ TB ∘ f)`. By `hfT` and `p ∘ f = id`,
`p ∘ TB ∘ f = TA`. For `SC`, cyclicity with `g ∘ TB` gives
`trace SC = trace (g ∘ TB ∘ s)`. By `hgT` and `g ∘ s = id`,
`g ∘ TB ∘ s = TC`.

The argument needs no splitting compatible with `TB` and no
finite-dimensionality of `A`, `B` or `C`. It uses no compact-open fixed
vectors, representation classification or character independence.

## Dependencies

Library: `Langlands.finiteRankEnd`, `Langlands.FiniteRankEnd.trace` and
`Langlands.FiniteRankEnd.trace_eq_of_factorization`. Mathlib:
`LinearMap.HasNoetherianRange.comp_left`, `.comp_right`,
`LinearMap.exists_leftInverse_of_injective` (from
`Mathlib.LinearAlgebra.Basis.VectorSpace`) and
`LinearMap.exists_rightInverse_of_surjective` (from
`Mathlib.Algebra.Module.Projective`). The module imports exactly
`Langlands.LinearAlgebra.FiniteRankTrace` and these two Mathlib modules.
