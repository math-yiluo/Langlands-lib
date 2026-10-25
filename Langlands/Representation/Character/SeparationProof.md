# Proof of character separation for irreducible admissible representations

Author: Worker 203. The theorem `Langlands.characterSeparation` proves the
published `Langlands.CharacterSeparationStatement.{uG,uV,uW}` from
`Langlands.Representation.Character.SeparationStatement`. It keeps the three
independent universes, so the group and the two carriers have unrelated
universes. It adds no hypotheses. In particular there is no unimodularity,
sigma-compactness, genericity, compact-coefficient condition,
finite-dimensional carrier, carrier topology or supplied equivalence. The
regularity instance `μ.Regular` of the target is introduced but never used. The
proof uses only the Haar-measure instance, through the Library's Hecke corner.

## Reverse implication

An equivariant linear equivalence `E : V ≃ₗ[ℂ] W` gives equal characters by the
published `Character.distribution_eq_of_equivariant`.

## Forward implication

The main proof is `CharacterSeparation.nonempty_equiv_of_distribution_eq`. It
produces a `Representation.Equiv ρ σ`. The final theorem turns this into the
target's linear equivalence, and pointwise equivariance comes from
`isIntertwining'`.

1. **Nonzero carriers.** `nontrivial_of_isIrreducible`: an irreducible
   representation has a nontrivial carrier. Otherwise its submodule lattice,
   and so its subrepresentation lattice, would be a single point. That
   contradicts `⊥ ≠ ⊤`. Choose nonzero `v : V` and `w : W`.

2. **A common compact open subgroup.** `exists_compactOpen_fixed`: smoothness
   gives open subgroups `U` and `U'` that fix `v` and `w`. Then the published
   `Hecke.TestFunction.commonCompactOpenBiInvariance`, applied to the empty
   family and `U ⊓ U'`, gives a compact open subgroup `K ≤ U ⊓ U'`. So
   `v ∈ V^K` and `w ∈ W^K`, and both fixed spaces are nonzero. Admissibility
   makes them finite-dimensional.

3. **The fixed spaces are simple corner modules.** Let `H_K` be the actual
   Hecke corner `Hecke.HeckeAlgebra.Corner μ K hK`. It acts on `V^K` through
   `Hecke.cornerModule`, compatibly with the complex scalars
   (`Hecke.cornerModule_isScalarTower`). The proof reuses the published
   `CompactCoefficientClass.isSimpleModule_fixedVectors` from
   `Langlands.Representation.CompactCoefficient.FixedLevelFiniteness`.
   Despite its namespace, that theorem requires no compact-coefficient
   hypothesis and applies to carriers in arbitrary universes. The separate
   helper `exists_cornerAction_eq` remains: it realizes any fixed vector
   from a nonzero fixed vector using `Hecke.orbitCombination_surjective`,
   `Hecke.cornerAction_translateCombination` and `Hecke.fixedProjection_fixed`.
   The proof does not use the separate, unproven proposition
   `Hecke.CornerFixedVectorsSimplicityStatement`.

4. **Characters on the corner.** `distribution_corner`: for `e ∈ H_K`, the
   character at the test function underlying `e` is the trace of the corner
   action of `e` on `V^K`. This is the published
   `Character.distribution_eq_fixedVectors` with `J = K`, using
   bi-invariance of corner elements, followed by unfolding the corner action.
   So equal characters give equal traces of every element of `H_K` on `V^K`
   and `W^K`.

5. **Finite-dimensional separation.** `nonempty_linearEquiv_of_trace_eq` is a
   general algebra lemma. Let `A` be a complex algebra and let `M`, `N` be
   simple `A`-modules that are finite-dimensional over `ℂ`. If every `r : A`
   has the same trace on `M` and on `N`, then `M ≃ₗ[A] N`. Suppose not. By
   Schur's lemma (`LinearMap.bijective_or_eq_zero`), every `A`-linear map
   `M → N` or `N → M` is zero. The module `M × N` is semisimple, as the sum of
   the ranges of `inl` and `inr`. The projection `x ↦ (x.1, 0)` commutes with
   every `A`-endomorphism of `M × N`, because the off-diagonal components of
   such an endomorphism vanish. Mathlib's `jacobson_density`, applied to the
   finite set of basis vectors `(b_i, 0)` and `(0, b'_j)`, then gives `r : A`
   that acts as the identity on `M` and as zero on `N`. Comparing traces gives
   `finrank ℂ M = 0`, which is impossible for a simple module.

6. **Recovering the representation.** Steps 3–5 give an `H_K`-linear
   isomorphism `φ : V^K ≃ W^K`. Put `a = v` and `b = φ a`; both are nonzero.
   Since `φ` commutes with the corner action, an element `e ∈ H_K` kills `a`
   exactly when it kills `b`. The published
   `Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff`, the annihilator form
   of Bernstein–Zelevinsky 2.10(b), then gives `Nonempty (ρ.Equiv σ)`.

## Literature

The source is I. N. Bernstein and A. V. Zelevinsky, *Representations of the group
GL(n,F) where F is a non-archimedean local field*, Russian Math. Surveys 31:3
(1976), registered as `bernstein-zelevinsky-1976-representations-gln`.
Corollary 2.20 (printed/PDF p.21) is the target. It follows from
Proposition 2.19, whose proof does three things: it chooses one open compact
subgroup with nonzero fixed vectors in every representation, uses 2.10 to make
the fixed spaces irreducible and pairwise inequivalent Hecke-corner modules,
and then cites linear independence of characters of inequivalent irreducible
finite-dimensional representations. The Lean proof follows the same route for
two representations. It proves the finite-dimensional step as the two-module
Jacobson-density argument of step 5, instead of citing the general linear
independence. It reuses the Library's proved corner-simplicity and annihilator
results for the 2.10 ingredients.
