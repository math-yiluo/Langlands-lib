# Stable images of proper adic cohomology

`ProperAdicCohomologyStableImageStatement.{u}` states the third conclusion of
Stacks Project Lemma 30.20.4 (tag 02OB), in every universe, for the actual
category of structure-sheaf modules.

Let `R` be a noetherian commutative ring, `I` any ideal of `R`, and
`f : X ⟶ Spec R` a proper morphism. Let `M` be a quasi-coherent module whose
sections on every affine open are finite over that open's ring. Since a
proper scheme over a noetherian affine scheme is locally noetherian, these
are the source's coherent-module hypotheses. For each cohomological degree
`p`, the proposition asserts that there is one nonnegative integer `c`
such that, for every `n` and `k` with `n + c ≤ k`,

\[
\operatorname{im}\bigl(H^p(X,M/I^kM)\longrightarrow H^p(X,M/I^nM)\bigr)
=
\operatorname{im}\bigl(H^p(X,M)\longrightarrow H^p(X,M/I^nM)\bigr).
\]

The bound may depend on the ring, ideal, scheme, morphism, module and
cohomological degree, but not on either quotient index. There is no
local-ring, completeness, flatness or projectivity assumption.

The quotients and maps are those of `IdealAdicQuotients`: `I^n M` is the
sheafification of the structure-sheaf-linear spans of products of elements
of `I^n` with sections of `M`, and `M/I^n M` is the cokernel of its monic
inclusion into `M`. The transition is induced by `I^k ≤ I^n` for `n ≤ k`.
The other map is the canonical quotient projection. The zero index uses
`I^0 = ⊤`, as in the source's nonnegative inverse system.

`DerivedSections.relativeCohomology f p` is the actual right-derived
functor of global sections over `R`. Its maps are `R`-linear, and the
displayed equality is encoded as equality of their `LinearMap.range`s
inside the same actual cohomology module of `M/I^n M`. Thus the images
refer to the canonical quotient and transition maps.

This file gives a proposition, not a proof. It asserts precisely the
stable-image conclusion (3); it does not separately assert the kernel
estimate (1) or construct completions or a formal-functions isomorphism.
It supplies a general prerequisite for eventual lifting from an ample
fibre.

Source: `stacks-formal-functions-stable-images-2026-11-04`, content SHA256
`462a0b605686ecd339d74357887ac1c307c8924ff49af7cdec720d081710ea4f`,
`02OB.txt`, Lemma 30.20.4, conclusion (3). The convention for local ideal
multiples is in the opening paragraphs of `02O7.txt`, Section 30.20.
