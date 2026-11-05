# Kernels of sectioned subgroups and torus envelopes

This module is internal derived content. It combines the Library's actual kernel,
represented subgroup factorization, split-kernel scheme retraction, smoothness
criterion for a surjective identity differential, and closed-subgroup unipotence.
It does not assert the existence of a torus quotient or section.

For a closed homomorphism `h : H → G` and a quotient map `q : G → Q`, the
restricted full kernel is the actual group scheme `kernel (h ≫ q)`.
Given a monomorphic representative `n : N → G` with the same all-test range as
`kernelι q`, `SectionedSubgroupKernel.toAmbientKernel` is its canonical map into
`N`. Its composite with `n` is the actual kernel inclusion followed by `h`.
Its range equals `(range h).comap n` on every relative scheme, including
nonreduced tests. When both original inclusions are closed and `Q` is separated,
this map into `N` is closed.

Over a field, suppose `H` and `Q` are affine of locally finite type, `H` is smooth,
and a homomorphism `sH : Q → H` splits `h ≫ q`. Composing tangent points with `sH`
proves surjectivity of the actual identity differential. The published differential
criterion then proves smoothness of the projection. The section proves
surjectivity on underlying spaces, so the restriction is an fppf quotient by
its full scheme-theoretic kernel.

If `H` is also connected, the published split-kernel scheme retraction proves
smoothness and connectedness of this same full kernel. Its closed inclusion in
the affine source proves affineness. If the ambient representative `N` is affine,
of locally finite type and unipotent, the closed-subgroup theorem proves the
restricted kernel unipotent. Over a perfect field the published
`perfectFieldUnipotentSplit` gives its finite represented split series.

For an actual torus section `s : Q → G`, closedness and the torus property
allow the Library's canonical `D.torusFactor` to lift it to any representative
`D` of the unchanged closed torus envelope. Associativity and the original
section identity prove that the lifted homomorphism is still a section.

These are conditional construction and geometry lemmas. They do not prove the
finite-field solvable envelope normality statement, representability or smoothness
of the envelope, or the existence of a solvable torus quotient with a section.
