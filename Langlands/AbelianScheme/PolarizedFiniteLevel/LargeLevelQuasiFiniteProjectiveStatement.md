# Eventual locally quasi-finite projective maps from fine moduli schemes of ordinary polarized full-level data

`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiFiniteProjectiveStatement`
is a proposition definition. It is a statement only. The module proves nothing.

## The statement

Fix `P : Prerequisites.{0}` and natural numbers `g d` with `0 < g` and `0 < d`.
The statement says that some natural number `N` has the following property. Let
`n ≥ N` with `hn : 3 ≤ n`, and let `X : LevelBase n` be any level base that
represents the published functor `moduliFunctor P g d n hd hn`, that is, there
is a natural isomorphism `uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn`.
Then there are a natural number `m` and a morphism
`j : X.obj ⟶ ProjectiveSpace ℤ[1/n] m` (the Library's projective space
`Langlands.AlgebraicGeometry.ProjectiveSpace`) with two properties:

- `j` is locally quasi-finite (Mathlib's `LocallyQuasiFinite`), and
- `j ≫ projectiveSpaceToSpec ℤ[1/n] m = X.toLocalizationSpec`, so `j` is a
  morphism over `Spec ℤ[1/n]`.

Here `ℤ[1/n]` is `Localization.Away (n : ℤ)`. The statement asks neither that
`j` be an immersion nor that it be quasi-compact or separated.

The hypotheses and the quantifier structure are those of the published target
`LargeLevelQuasiProjectivityStatement` in the same namespace.

## Provenance

This is a derived intermediate statement. It is a weakening of the published
target `LargeLevelQuasiProjectivityStatement`, whose source is GIT Theorem 7.9:

Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd edition, registered
source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`
(content SHA-256
`3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`), Theorem 7.9
(printed p.139, PDF p.152):

> If `n > 6^g · d · √(g!)`, the fine moduli scheme `A_{g,d,n}` for abelian
> varieties of dimension `g`, with level `n` structure and polarization of
> degree `d` exists. It is quasi-projective over `Spec(ℤ)`.

The theorem prints "polarization of degree `d`". The functor it refers to is
the functor `𝒜_{g,d,n}` of Chapter 7, Definitions 7.2 and 7.3 (printed p.129,
PDF p.142). There the polarization has degree `d²`, that is, `ω_*(𝒪_X)` is
locally free of rank `d²`. The published `moduliFunctor P g d n hd hn` uses the
convention of the definitions, degree `d²`, and so does this statement.

Quasi-projective is meant in the EGA sense. The registered Stacks snapshot
`stacks-quasi-projective-ample-finite-type-2026-11-19` (content SHA-256
`112270b8b6f437c38228945f1221ccc306b020c84ff13bc87f6c2c6efda77692`), Definition
29.41.1 (file `Stacks-29.41-01VV.html`), reads: "`f` is quasi-projective if `f` is
of finite type and there exists an `f`-relatively ample invertible
`O_X`-module."

The target gives, with the same bound `N`, an immersion
`i : X.obj ⟶ ProjectiveSpace ℤ[1/n] m` over `Spec ℤ[1/n]`. Every immersion is
locally quasi-finite (Mathlib's low-priority instance
`[IsImmersion f] : LocallyQuasiFinite f` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`). So `j = i` satisfies the
statement. This implication is not formalized here.

## Role

This statement is one of three moduli inputs of the proved definition
`largeLevelAmple_of_quasiFiniteProjective` (module
`LargeLevelAmpleQuasiFiniteReduction`). Its four inputs are
`Picard.QuasiFiniteAmplePullbackStatement.{0}` (a general statement),
`LargeLevelFiniteTypeStatement`, `LargeLevelSeparatedStatement` and this
statement. From them it proves `LargeLevelAmpleStatement`.

The target `LargeLevelQuasiProjectivityStatement` then follows by the proved
definition `largeLevelQuasiProjectivity_of_ample` (module
`LargeLevelQuasiProjectivityAmpleReduction`). That definition has two explicit
inputs:

- `Picard.AmpleHQuasiProjectiveStatement.{0}`, the general statement that an
  ample line bundle on a scheme locally of finite type over an affine base gives
  an immersion into projective space (Stacks Lemma 29.40.3, Tag 01VS);
- `LargeLevelAmpleStatement`.

## Intended proof (not established)

Nothing in this section is proved or claimed. It records the route a proof is
expected to take and marks the steps that are still open. A proof is expected to
avoid the immersion property and to use bracket sections of one line bundle.

1. **Brackets.** Let `π : A → X` be the universal abelian scheme and `L` the
   diagonal Poincaré bundle of its polarization, `L^Δ(ω)` in GIT Definition 7.5
   (printed p.130, PDF p.143); in the Library this is `Datum.canonicalBundle`.
   Its tensor cube `L³` is `Datum.cubicBundle`, and `E = π_* L³` is
   `Datum.rigidificationModule`, expected to be locally free of rank `m + 1`
   (in the Library's `CubicDirectImageStatement` the rank is `6^g · d`). Let
   `P_r` be the torsion sections. For `m + 1` labels `r_0, …, r_m`, the
   determinant of the evaluation of `E` at `P_{r_0}, …, P_{r_m}` is a section of
   `det(E)^{-1} ⊗ P_{r_0}^* L³ ⊗ ⋯ ⊗ P_{r_m}^* L³`. So the brackets, the frame
   loci and the hyperplane bound below all use the same cubic bundle `L³`.
2. **Balanced monomials (to establish).** A monomial in brackets has a weight
   at each label. Only monomials with the same weight `k` at every label are
   sections of one line bundle `K_k`, a power of `det(E)^{-1}` tensored with
   `(⊗_r P_r^* L³)^k`. The products of the brackets of a single frame from
   `FrameLocus` are not balanced: they have positive weight only at the frame's
   labels. So the frame-chart cover (`FrameLocusCoverStatement`) does not by
   itself give a balanced monomial that is nonzero at a point. For example (from
   the review of an earlier version of this candidate), take seven points of
   `P²`: five on the line `z = 0`, including `[1:0:0]` and `[0:1:0]`, and
   `[0:0:1]`, `[1:1:1]`. The last four form a frame. A monomial of the same
   positive weight `k > 0` at all seven labels has `7k/3` brackets, and a
   nonzero bracket contains at most two of the five collinear labels. That
   allows at most `14k/3` of the `5k` required incidences, so every balanced
   monomial of positive weight vanishes there. (At `k = 0` the empty product is
   the constant section `1`, which gives no map.)
3. **Nonvanishing at each point (to establish).** The source's route is
   stability. At each geometric point the torsion configuration in `P(E)` is
   expected to be stable in the sense of GIT Chapter 3, Proposition 3.4
   (printed p.73): for every proper linear subspace, the fraction of points in
   it is less than the fraction `(dim + 1)/(dim P(E) + 1)`.
   The hyperplane count of GIT Proposition 7.7 (in the Library as
   `CubicTorsionHyperplaneBoundStatement`) is the input for this when `n` is
   large. GIT Proposition 3.6 and Corollary 3.7 (printed pp.73–76) then give
   monomials in the brackets that do not vanish at the point, and their product
   is balanced.
4. **Common degree (to establish).** The map `j` needs one degree `k` such that
   the balanced monomials of degree `k` have no common zero on `X`. Passing from
   pointwise nonvanishing monomials of varying degree to a single degree is a
   separate step.
5. **Finite fibres (to establish).** The ratios of balanced monomials are
   invariants of the torsion configuration up to `PGL`. A locally quasi-finite
   morphism has discrete fibres (Mathlib's
   `Scheme.Hom.isDiscrete_preimage_singleton`), but discreteness is not the
   criterion used here. A sufficient criterion is Mathlib's
   `LocallyQuasiFinite.of_finite_preimage_singleton`: `j` is locally of finite
   type and every fibre `j ⁻¹' {x}` is finite. Here `j` is locally of finite
   type because `X` is (the separate input `LargeLevelFiniteTypeStatement`; a
   morphism between schemes locally of finite type over `Spec ℤ[1/n]` is
   locally of finite type). Finite fibres reduce to finite fibres over
   geometric points, that is, over an algebraically closed field a datum is
   determined up to finitely many choices by these invariants. Recovering the
   configuration coordinates from the invariants is part of this step. GIT
   Theorem 3.8 (printed p.76) is the corresponding step of the source.
