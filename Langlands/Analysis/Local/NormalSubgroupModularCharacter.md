# Right Haar lifting and closed normal modular characters

This internal construction supplies the closed normal subgroup step used in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §3.6,
Lemma 3.6.4, printed pp.89–90. Its proof is derived directly from the Library's
real quotient averaging operator, the Riesz representation theorem and Haar
uniqueness. The construction is not a definition copied from the book.
The October 2026 errata has no correction to §3.6.

All declarations are in `Langlands.QuotientIntegration`. The ambient group
`G : Type u` has its supplied locally compact Hausdorff group topology and Borel
measurable structure. The subgroup `H` is closed and has a Borel measurable
structure on its subtype topology. The actual left quotient is `H \ G`, with
representatives `H * g` and the quotient topology.

## The constructed lift

`rightQuotientLift H hH η ν` is the Riesz measure whose compact real test
integral is

\[
\int_{H\backslash G}\int_H f(hg)\,d\eta(h)\,d\nu(Hg).
\]

Here `η` is right invariant and finite on compact sets, and `ν` is finite on
compact sets. No left invariance of `η` is assumed. The existing averaging
operator descends because right translation preserves `η`, and has compact
support and continuity because `H` is closed. `integral_rightQuotientLift`
records the defining test integral. The lift is regular.

`rightQuotientLift_rightInvariant` proves right invariance of the lift whenever
`ν` is preserved by every actual right translation of the quotient.
`rightQuotientLift_ne_zero` proves nonzeroness when both input measures are
positive on nonempty open sets. It chooses a nonnegative compact continuous
test positive at the identity; its subgroup average is positive at the identity
coset, so its integral over the quotient is positive.

For normal `H`, `normalQuotientRightHaar H` transports the inverse of left Haar
measure on the quotient group `G / H` to `H \ G` along the existing canonical
homeomorphism. It is regular, positive on nonempty open sets and preserved by
all quotient right translations. This definition uses the supplied Borel
structures on both quotient carriers.

## Modular compatibility

`map_mul_left_invHaar` and `integral_mul_left_invHaar` describe left translation
of inverse left Haar measure. With Mathlib's convention
`map (fun x => x * g) μ = modularCharacter g • μ`, the left-translation scalar
for `μ.inv` is `modularCharacter g⁻¹`.

`modularCharacter_normalSubgroup H hH h` proves

\[
\Delta_H(h)=\Delta_G(h),\qquad h\in H,
\]

for every closed normal subgroup, with neither group assumed unimodular.
The proof constructs the lift using inverse left Haar on `H` and
`normalQuotientRightHaar H`. Its inverse is a nonzero regular left Haar measure
on `G`. A nonzero compact test integral detects its scaling under left
translation by `h⁻¹`. Subgroup integration gives the scalar `Δ_H(h)`, whereas
ambient Haar uniqueness gives `Δ_G(h)`; cancellation identifies them.
Local compactness of `H` is obtained from closedness.

This unit establishes a general analytic construction and its compatibility
property. It does not identify the adelic modular character with an algebraic
character norm, prove triviality of a reductive adjoint determinant, or prove
the universal adelic Haar-unimodularity target.
