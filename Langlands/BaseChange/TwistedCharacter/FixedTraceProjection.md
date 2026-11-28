# Trace pairings and projections to the fixed algebra

Let `R` be a finite-dimensional associative algebra over a field `F`, let `α` be an algebra automorphism, and let `S` be its fixed subalgebra. Give `R` the bilinear form `B(x,y) = Tr(L_(xy))` from left multiplication and give `S` the restriction of `B`. `FixedTraceProjectionStatement` states that an `F`-linear map `p : R → S` with `p|S = id` and `p ∘ α = p` is adjoint to the inclusion `S → R` for these forms.

In `fixedTraceProjection`, the kernel of `p` is stable under `α`. The endomorphism `α − 1` of this kernel is injective since a fixed vector in the kernel is zero. Finite dimensionality gives surjectivity, so every `x − p(x)` is of the form `α(z) − z` for a vector in the kernel. This difference pairs to zero with each fixed `y`, since conjugating the left multiplication operator by `α` preserves trace. Thus `B(p(x),y) = B(x,y)`. Applying an additive character to the identity gives adjointness of the corresponding bicharacters used in the dual-lattice computation for semisimple descent. [Clozel, *Characters of non-connected, reductive p-adic groups*, §3.4 and proof of Lemma 9 in §3.6](https://doi.org/10.4153/CJM-1987-008-3)

The theorem `isInvariantPairing_regularTraceForm` gives symmetry, nondegeneracy and unit-conjugation invariance of the ambient form for semisimple `R` in characteristic zero. It uses cyclicity of trace for symmetry and conjugation invariance, and applies `adjointFixedTracePairing_nondegenerate` to the identity automorphism for nondegeneracy.

`regularTraceForm_automorphism` shows that every algebra automorphism
preserves the ambient regular trace form. Left multiplication by the
image of an element is conjugate to left multiplication by that element,
and conjugation preserves the linear-map trace.
