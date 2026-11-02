# Actual positive-torus chambers for restricted relative roots

This is an internal adapter between actual adelic torus points, the normalized
idele norm, and the shared relative-root definitions. Let `F` be any number field,
`T₀` and `T` commutative group schemes over `F`, and `j : T₀ ⟶ T` an actual
homomorphism. `normCharacter` is the continuous character obtained by composing
actual rational-character evaluation with `IdeleAbsoluteValue.full F`.
`normCharacter_pullback` proves that evaluating the restricted character `j ≫ χ`
is the same as first mapping the actual point through `j`.

The weak and strict character chambers are sets in the **actual subtype**
`intrinsicSubgroup F T₀`. For a set `Δ` of characters of `T` and positive thresholds
`b χ`, they impose, respectively,

```
b χ ≤ |(j ≫ χ)(a)|_A     and     b χ < |(j ≫ χ)(a)|_A
```

for every `χ ∈ Δ`. These definitions need no splitting and allow an empty
character set. The strict chamber is contained in the weak chamber; both become
the whole positive subgroup when `Δ` is empty, and enlarging `Δ` decreases them.
Continuity of the actual normalized characters proves that weak chambers are
closed. A finite character set makes the strict chamber open **in the positive
subgroup**; ambient openness is not asserted. Finiteness is an explicit
hypothesis, not a claimed relative-root structure theorem.

Given a genuine splitting `e : T₀ ≅ G_m^I` with finite `I`, `fullIntrinsic` is the
existing equal-archimedean-scalar, finite-component-one parametrization with
codomain restricted to the intrinsic subgroup. The previously proved equality
of the coordinate and intrinsic subgroups proves it surjective.
`normCharacter_fullIntrinsic` gives the exact normalization:

```
|(j ≫ χ)(fullIntrinsic x)|_A =
  (∏ i, x i ^ characterExponents (j ≫ χ) i) ^ [F : ℚ].
```

The coordinate membership lemmas retain this degree. The two image equalities
show that any supplied splitting computes exactly the same intrinsic chamber;
thus changing coordinates changes neither chamber. Empty rank is retained.
The proofs use the actual character monomial formula and scalar idele norm
formula already established in `PositiveRealTorus`.

For an affine group scheme `G`, a morphism `i : T ⟶ G`, and a cocharacter `ν`,
`weakSimpleRootChamber` and `strictSimpleRootChamber` specialize to
`simpleRelativeRoots i ν`. The former has a common positive threshold `t`; the
latter has explicitly indexed thresholds. `basedStrictSimpleRootChamber`
computes these thresholds by normalized character evaluation at an actual
adelic point of `T`. These are meaningful constructions without maximal
splitness, connected reductivity or genericity. Identification with the roots
of a specified minimal parabolic requires the corresponding structural
theorems. In particular, `j` is an actual morphism, not a relabeling of a root set.
No assertion is made that its character pullback is injective.

The source motivation is:

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), source
  `getz-hahn-2024-automorphic-representations`, §2.7, printed pp.71–72:
  the simple roots are characters of a maximal split torus `T = T₀ Z₀`,
  while the chamber lies in the positive subgroup of the derived torus `T₀`.
  This requires the actual restriction along `j`. The source uses weak
  inequalities with the normalized archimedean product. Finite components of
  these positive scalar points are one.
- Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  source `moeglin-waldspurger-1995-spectral-decomposition`, I.1.4,
  printed pp.5–7, I.1.6, printed p.11, and I.2.1, printed pp.18–20:
  normalized positive adelic characters are defined in I.1.4; I.1.6 treats
  roots as elements of `Re X_M₀` by default. I.2.1 embeds a positive scalar
  equally at all infinite places and as one at finite places, then uses
  strict inequalities `a^α > t₀^α`. Its p.19 argument explicitly distinguishes
  algebraic root evaluation from normalized positive-character evaluation.
  Our degree formula preserves that distinction. The based strict chamber
  here permits a reference **torus point**; the source's arbitrary reference
  `t₀ ∈ M₀` requires the additional rational-character/Levi comparison.

These source passages motivate the inequalities. The implementation is a
derived internal construction on `PositiveRealTorusIntrinsic`,
`PositiveRealTorusTopology`, `PositiveRealTorusEmbedding` and the unchanged
shared `Rational.StandardParabolic` interface of Worker 1225. It is not a
complete Siegel set: compact unipotent and Levi factors, a suitable maximal
compact, actual minimal-parabolic comparisons, reduction/coverage, finite volume
and the analytic Haar-modulus theorem remain separate obligations.
