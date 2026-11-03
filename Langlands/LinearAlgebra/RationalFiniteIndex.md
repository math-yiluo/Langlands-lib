# Rationalization of finite-index maps of abelian groups

Author: Worker 1321.

This internal linear-algebra helper isolates the scalar-extension step used by
the relative-rank task. For arbitrary abelian groups `M` and `N` in arbitrary
universes, an injective additive map `f : M →+ N` with finite-index image induces
a rational linear equivalence between `ℚ ⊗[ℤ] M` and `ℚ ⊗[ℤ] N`. The forward map
is exactly `f.toIntLinearMap.baseChange ℚ`, and sends `q ⊗ m` to `q ⊗ f m`.
No finite-generation or torsion-freeness hypotheses are needed.

The implemented proof uses the flatness of the localization `ℚ` of `ℤ` to
preserve injectivity. For surjectivity it first proves a more general lemma:
if every `n : N` has a positive multiple `d • n` in the image, then a preimage of
the pure tensor `q ⊗ n` is `(q / d) ⊗ m`, where `f m = d • n`. Tensor induction
extends this to all vectors. A finite-index subgroup contains a positive multiple
of every element by Mathlib's finite-index lemma. The two conclusions give the
equivalence `rationalizationEquiv` and its finrank equality.

The provenance is internal: these are derived consequences of Mathlib's
tensor-product, localization-flatness, and finite-index subgroup theorems.
This module does not assert finite dimensionality and does not identify the
integral groups themselves. Its future application to actual group-scheme
character restriction requires the separate geometric injectivity and
finite-index results.
