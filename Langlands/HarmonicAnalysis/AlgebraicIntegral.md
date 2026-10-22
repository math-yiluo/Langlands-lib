# Algebraic integration of finite-image functions

The namespace `Langlands.HarmonicAnalysis.AlgebraicIntegral` constructs an
integral for Mathlib's `MeasureTheory.SimpleFunc X V`. The measurable domain
`X : Type u` carries an arbitrary measure `μ`. The value space `V : Type v`
has exactly `AddCommGroup V` and `Module ℂ V`. It has no measurable-space,
topology, norm, dimension, or completeness hypothesis. The domain and value
universes are independent. None of the results assumes sigma-finiteness.

## Definition and zero convention

`integral μ f` is the actual finite fiber sum

\[
  \sum_{v\in f.\mathrm{range}}
    \operatorname{ofReal}\bigl((\mu(f^{-1}\{v\})).\mathrm{toReal}\bigr)\,v.
\]

Here `f.range` is Mathlib's finite range, and the displayed multiplication is
complex scalar multiplication on `V`. The definition is total on simple
functions. Its intended linear domain is precisely those satisfying the
existing predicate `f.FinMeasSupp μ`, equivalently finite measure of the
nonzero support. Each nonzero fiber then has finite measure. The zero fiber
may have infinite measure: its term is zero because its value is zero.
`ENNReal.toReal` also sends infinity to zero; outside the finite-support
hypotheses, the definition is only this totalized fiber sum and no general
linearity is asserted.

`integral_eq_sum_of_subset` computes the same integral over any finite value
set containing all nonzero values of `f`. No support hypothesis is required.
It proves both independence of enlarged lists and permission to insert or
omit zero. Extra values have empty fibers. `integral_zero` follows by taking
the value list to be empty.

## Construction laws

`integral_map` is the main regrouping result. For a simple function
`f : SimpleFunc X A`, with only `Zero A` on the intermediate value type,
finite-measure support, and any map `g : A → V` satisfying `g 0 = 0`, it says

\[
  I_\mu(g\circ f)
  =\sum_{a\in f.\mathrm{range}}
     \operatorname{ofReal}\bigl((\mu(f^{-1}\{a\})).\mathrm{toReal}\bigr)\,g(a).
\]

The proof groups the finite sum by the image of `g`. Groups with value zero
vanish. In a nonzero group every original value is nonzero, so its fiber has
finite measure; finite additivity and `ENNReal.toReal_sum` justify the
regrouping. No algebraic law of `g` is assumed here.

`integral_add` applies this regrouping to the joint fibers `SimpleFunc.pair f g`;
both functions must have finite-measure support. `integral_smul` proves complex
homogeneity with the same hypothesis on the function. `integral_linearMap`
proves

\[
  I_\mu(L\circ f)=L(I_\mu(f))
\]

for every complex linear map `L : V →ₗ[ℂ] W` and finite-support `f`.
The carrier `W : Type w` has its own independent universe, additive commutative
group, and complex module structure; no continuity hypothesis occurs.

`finiteSupportSubmodule μ` is the submodule of actual simple functions with
finite-measure support. `integralLinear μ` bundles the proved addition and
scalar laws on this submodule. Its fields are established theorems about the
fiber sum, not supplied assumptions. `finMeasSupp_sum` and `integral_sum`
provide the corresponding laws for a finite family when each summand has
finite-measure support.

## Indicators, partitions, and refinement

For a measurable set `s` and any value `v`, `integral_indicator_const` evaluates
`(SimpleFunc.const X v).restrict s` as
`((μ s).toReal : ℂ) • v`. The equality also holds with the totalized convention
on infinite-measure sets. `finMeasSupp_indicator_const` proves finite-measure
support under the exact condition `v ≠ 0 → μ s < ⊤`.

`integral_eq_of_indicator_presentation` handles a finite family of measurable
sets `s i`, values `v i`, and a pointwise presentation

\[
  f(x)=\sum_{i\in t}1_{s_i}(x)v_i.
\]

It assumes finite measure only for cells whose value is nonzero. The integral
is then `∑ i ∈ t, ((μ (s i)).toReal : ℂ) • v i`. The proof first establishes
equality of the actual simple functions, then applies finite-sum linearity
and the indicator formula. The cells need not be disjoint.

`integral_eq_of_partition` specializes this result to pairwise disjoint cells
indexed by the finite set `t`. They must cover the nonzero support of `f`,
and `f` must equal `v i` on each `s i`. Measurability and the same conditional
finite-measure hypothesis are explicit. Points outside all cells have value
zero; zero-valued cells may have infinite measure.

`presentation_independent` compares two finite indicator presentations of the
same actual function, allowing different index types and different values.
Both weighted sums equal its integral. This proves independence under every
finite measurable partition refinement satisfying the displayed presentation
and finite-measure conditions, including repeated values and zero cells.

## Scalar comparison and change of variables

`integral_eq_bochner` identifies `integral μ f` with `∫ x, f x ∂μ` when
`f : SimpleFunc X ℂ` has finite-measure support. Mathlib supplies integrability
from that predicate. The proof uses its genuine Bochner simple-function sum
formula and identifies real scalar multiplication on `ℂ` with multiplication
by the corresponding complex scalar.

`integral_comp` gives the pushforward identity
`integral μ (f.comp e he) = integral (Measure.map e μ) f` for every measurable
map `e : X → Y`, with independently universe-polymorphic measurable `Y`.
It compares fiber measures using the pushforward formula and expands the
pullback sum to `f.range`. It needs no finite-support hypothesis.
`integral_comp_measurePreserving` replaces the pushforward by a measure `ν`
under `MeasurePreserving e μ ν`. In particular it applies to every
measure-preserving measurable equivalence. The companion
`finMeasSupp_comp_measurePreserving` proves that the pullback has finite-measure
support exactly when the original function does, by equality of support
measures.

## Provenance and scope

This is an internal foundational construction for algebraic smooth-representation
integration. Its detailed proofs are not attributed to Flath or another original
literature source. It reuses the project's pinned Mathlib definitions and
measure identities in `MeasureTheory/Function/SimpleFunc.lean`, together with
the genuine scalar comparison in `MeasureTheory/Integral/Bochner/Basic.lean`.
All mathematical laws above are proved intrinsically from the finite fiber sum.
The module constructs no Haar convolution, orbit maps, compact-open invariance,
or Hecke action; those are separate consumers of this interface.
