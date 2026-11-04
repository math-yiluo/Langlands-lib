# Actual closed-subscheme families under field base change

This derived construction supplies field-base-change comparisons for the finite
closed-cover and intersection argument in Stacks Project Lemma 37.28.4 (055G),
last paragraph of the proof. It supports the geometric-connectedness input to
Conrad's Theorem 3.4(2). The registered source is
`stacks-fibre-constructibility-local-dimension-2026-11-04`, retained `055C.html`.

The current construction is `baseChangeSubschemeRanges p g`: the family of actual
ranges of the projections `pullback (g i) p ⟶ T`, for `p : T ⟶ X` and actual
morphisms `g i : Z i ⟶ X`. The range identity from Mathlib identifies each range
with the inverse image of the original range under `p`. On actual residue-field
fibres this agrees with `fiberSubschemeSets`.

Surjectivity of `p` preserves and reflects the nonemptiness of each pairwise
intersection and reflects coverage of the whole space. Coverage is preserved
without surjectivity. These are proved by the actual pullback range identity
and pointwise surjectivity. The incidence-chain comparison uses the imported
finite-chain transport theorem with the identity on the index type; it does not
require the family to be finite. There are no finiteness, closedness or topology assumptions
on the family beyond being scheme morphisms.

For schemes over a field, every morphism between field spectra is surjective:
the target has one scheme point and the source is nonempty. Surjectivity is
stable under scheme base change. Thus the actual projection from any field base
change is surjective, and both coverage and pairwise incidence are preserved
and reflected for the actual base-changed family. The field morphism is
arbitrary; no finite, separable, algebraic or algebraically closed condition is
imposed. The fields and schemes have common arbitrary universe `u`; the index
type has independent universe `v`.

This is an intrinsic construction with proved comparisons. It does not prove
geometric irreducibility spreading or identify nearby irreducible components.
