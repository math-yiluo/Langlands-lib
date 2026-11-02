# Smoothness descends along a surjective smooth map on the source

Author: Worker 293. Coauthor: Worker 1224, who ported the FLT smoothness lemmas
used here (modules under `Langlands.AnthropicFLT`, included in the same
contribution).

This module proves the Library statement
`Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentStatement.{u}` (Stacks
Project, Descent, Lemma 35.14.5, Tag 05B5, smoothness case with an etale
covering map) for every universe `u`.

## Declarations

- `Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp`:
  for schemes `W`, `X`, `S` in universe `u` and morphisms `p : W ⟶ X`,
  `g : X ⟶ S`, if `p` is smooth and surjective and `p ≫ g` is smooth, then `g`
  is smooth. This is the smooth case of Stacks Descent Lemma 35.14.4
  (Tag 02KM; Lemma 14.4 on p.43 of the registered PDF source
  `stacks-descent-ed88ff78-2026`). There are no affineness or
  quasi-compactness hypotheses.
- `Langlands.AlgebraicGeometry.smoothEtaleSourceDescent :
  SmoothEtaleSourceDescentStatement.{u}`: if `p` is etale and surjective and
  `p ≫ g` is smooth, then `g` is smooth. Mathlib's etale morphisms are smooth
  (an instance), so this is the previous theorem.

## Proof of the general theorem

The Lean proof does not follow the Stacks proof of 05B5, which descends
flatness and then checks smoothness on fibres. It checks smoothness at each
point of `X` through local rings. Steps 2 to 5 are adapted from the FLT proof
of the scheme lemma
`AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`
(see Provenance). That FLT lemma also assumes the covering map
quasi-compact and `g` locally of finite presentation. Its proof never uses
quasi-compactness. Step 1 proves local finite presentation of `g` here.

1. Smooth morphisms are flat and locally of finite presentation. So
   `Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp`
   (Stacks 02KL) makes `g` locally of finite presentation.
2. It remains to show that the smooth locus of `g` is all of `X`. Let
   `y ∈ X`. Since `p` is surjective, `y = p x` for some `x ∈ W`. Choose affine
   opens `U ⊆ S` containing `g y`, `V ⊆ g⁻¹ U` containing `y`, and
   `O ⊆ p⁻¹ V` containing `x`.
3. The ring maps `Γ(S, U) → Γ(X, V) → Γ(W, O)` form a scalar tower. The first
   is of finite presentation since `g` is locally of finite presentation. The
   second is smooth since `p` is smooth.
4. `p ≫ g` is smooth, so its stalk map at `x` is formally smooth. Mathlib's
   `AlgebraicGeometry.formallySmooth_stalkMap_iff` translates this into
   `Algebra.IsSmoothAt Γ(S, U) 𝔓`, where `𝔓` is the prime of `Γ(W, O)` at `x`.
   The prime `𝔭` of `Γ(X, V)` at `y` is the contraction of `𝔓`
   (`IsAffineOpen.comap_primeIdealOf_appLE`).
5. The ported FLT theorem `Algebra.IsSmoothAt.of_isSmoothAt_of_smooth`
   (module `Langlands.AnthropicFLT.Theorems.Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth`)
   gives `Algebra.IsSmoothAt Γ(S, U) 𝔭`. By `formallySmooth_stalkMap_iff`
   again, `y` lies in the smooth locus of `g`.

## Provenance

The target statement and the general theorem are Stacks results cited above.

Steps 2 to 5 adapt the proof of `solution` in
`P2M/Sol/S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; literature id
`anthropic-flt-complete-lean-source-6e837e75`). Licence: Apache License,
Version 2.0; Copyright 2026 Anthropic, PBC; copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. Worker 1224
ported that file in revision 2 of the draft of task
`83bb1057-d232-4d4d-8b0b-92eedc47eb0b`. The changes against the FLT proof are:

- the hypotheses `[QuasiCompact f]` and `[LocallyOfFinitePresentation g]`
  are removed; local finite presentation of `g` is proved in step 1;
- the schemes `X, Y, Z`, morphism `f` and open `W` are renamed `W, X, S`,
  `p` and `O`;
- `letI`/`haveI` are replaced by `let`/`have`;
- the theorem is named `smooth_of_smooth_of_surjective_of_smooth_comp` in the
  namespace `Langlands.AlgebraicGeometry`, and an attribution header is
  added to the Lean file.

The ten ported modules for step 5 are included in this contribution with
Lean text unchanged from that draft. Their paired Markdown files record the
FLT source, licence and port changes. The corollary `smoothEtaleSourceDescent`
is internal.
