# Algebraic properties of the generic Weil pullback

The closing theorem `Langlands.Weil.algebraicProperties` proves the complete
accepted proposition `Langlands.Weil.AlgebraicProperties.{u}`. The universe `u`
is arbitrary. The quantified group has exactly `[Group Γ] [TopologicalSpace Γ]`
and a continuous homomorphism `φ : Γ →ₜ* ProfiniteIntegers`. There are no
additional continuity, compactness, separation, or splitting hypotheses.
Surjectivity of `φ` is used only in the final conditional assertion.

## Implemented argument

The degree group is `Multiplicative ℤ`. To separate a nonidentity degree `g`,
put `n = |g.toAdd| + 1` and reduce the integer modulo `n`. This gives a group
homomorphism into the finite group `Multiplicative (ZMod n)`. If the image
were the identity, `ZMod.intCast_zmod_eq_zero_iff_dvd` and `Int.natCast_dvd`
would imply that `n` divides the positive natural number `|g.toAdd|`.
`Nat.le_of_dvd` would then give `|g.toAdd| + 1 ≤ |g.toAdd|`, a contradiction.

`degree_residuallyFinite` applies Mathlib's finite-homomorphism criterion
`Group.residuallyFinite_of_forall_exists_finite_monoidHom` to these witnesses.
`frobenius_injective` then applies
`ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite`.
The accepted `frobenius` definition reduces to that canonical map. Thus
the proof concerns the actual inverse limit of finite quotients used by
the accepted definition.

For a pullback element `w = (g,n)`, membership says `φ g = frobenius n`.
The remaining lemmas keep the coordinate arguments explicit:

1. `pullback_commutes` is extensionality followed by this membership equation.
2. `projection_injective` uses equality of first coordinates to equate the
   Frobenius images of the second coordinates, then applies
   `frobenius_injective` and subtype/product extensionality.
3. `projection_range` identifies both subgroup-membership conditions with
   existence of a degree `n` satisfying `frobenius n = φ g`. A witness
   gives the pullback pair `(g,n)`, and every pullback pair gives a witness.
4. `inertiaInclusion_injective` applies projection to an equality of
   included inertia elements. `projection_comp_inertiaInclusion` is
   extensionality and reflexivity: the first coordinate is unchanged.
5. `inertiaInclusion_range` proves both containments. An included inertia
   element has multiplicative degree `1`, which is additive integer zero.
   Conversely, for `degree φ w = 1`, the membership equation and
   `frobenius 1 = 1` put `projection φ w` in `ker φ`. Including this
   kernel element recovers `w` by its two coordinates.
6. `degree_surjective` uses a preimage of `frobenius n` under a surjective
   `φ`, and forms the corresponding pair of degree `n`.

The closing theorem introduces the target's group, its two instances, and
the homomorphism, then assembles all seven clauses after the initial
injectivity conjunct. All helpers are kept in this proof contribution.

## Exact dependencies and provenance

The target is statement artifact
`a1ca17e7-e6e7-40de-866f-a1db719cc6a2`, version 1, module
`Langlands.Weil.Algebraic`, published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab`. Its effective snapshot is
`bdbf7a14a6a5d5800958d1d758d3a90273f129253b41a85d6bca034255b7abb9`;
its checked proposition fingerprint is
`cf576391460530659e34a842c1b05c7da15ec77124156dff986d83fa3385ace4`.

The sole mathematical definition dependency is
`993e4326-4390-4fc8-94a7-82829061b1ea`, version 1, module
`Langlands.Weil.Pullback`, published at
`32f1fbf4cd19ab3f273133995b573b41c814aaff`, effective snapshot
`166bfc7cc53966e03598122ffa7dbf22278ed6f48089c91936b08cfa025221d7`.
Both exact artifacts were verified accepted, published, and current with
no missing or changed source files or unavailable dependencies.
No other project proof is imported.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The Mathlib audit used `GroupTheory/ResiduallyFinite.lean`,
`Topology/Algebra/Category/ProfiniteGrp/Completion.lean`,
`Data/ZMod/Basic.lean`, `Data/Int/Basic.lean`, and
`Algebra/Group/TypeTags/Hom.lean`, and
`Algebra/Group/TypeTags/Finite.lean`. The first two files already supply
the abstract residual-finiteness and completion-injectivity criteria;
the finite cyclic witness above supplies the integer case.

This is derived algebraic content of the accepted pair construction.
Its local-field motivation is Guy Henniart, *Representations du groupe de
Weil d'un corps local* (1980), Section 2.1 and the opening paragraph of
Section 2.2, printed page 158 / PDF page 5. The original was read together
with the hypotheses in Section 1.1, printed page 155 / PDF page 2:

- Literature ID: `henniart-1980-weil-representations`.
- SHA-256: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
- Retained file:
  `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`.

The source describes the integer-Frobenius preimage, inertia, and integer
quotient for the local Weil group. The present generic theorem is a
derivation for arbitrary `φ`; it retains surjectivity as a hypothesis
where the full degree image is asserted. It establishes no identification
with a field-theoretic Weil group or local reciprocity.

Worker 2 supplied the accepted construction and target and suggested the
finite-quotient and coordinate proof route. Worker 32 implemented this
Lean proof and its accompanying explanation. Compilation is development
evidence; acceptance additionally requires the registered independent proof
checker, independent semantic review, and current Library publication.
