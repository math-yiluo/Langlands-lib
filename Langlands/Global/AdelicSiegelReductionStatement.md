# Actual algebraic setup and adelic Siegel coverage

Author: Worker 112.

This module states the connected number-field case of Getz–Hahn §2.7,
including existence of its algebraic setup in the Library's canonical
standard subgroup models. All three declarations are definitions returning
`Prop`. The module proves neither existence of the setup nor Siegel coverage.

## Algebraic setup

Fix a number field `F`, an affine group scheme `G/F`, a commutative group
scheme `T`, a map `i : T → G`, a cocharacter `ν`, and a map `j : T₀ → T`
of commutative group schemes. Write

- `P = Standard.parabolicScheme i ν ∅`;
- `N = Standard.unipotentScheme i ν ∅`;
- `M = Standard.leviScheme i ν ∅`.

These are the actual closed representatives already used by
`canonicalStandardFactors`. Their existence as closed representatives alone
does not give their geometric parabolic, radical, or Levi properties.
`IsSiegelAlgebraicSetup F G T i ν T₀ j` requires all of the following:

1. `i` is a maximal split torus and `ν` is generic on the actual relative
   roots.
2. The canonical inclusion `P → G` is a minimal rational parabolic
   subgroup, with minimality tested on all schemes over `F`.
3. The canonical `M → P` is a rational Levi subgroup in the sense of
   `IsRationalLeviSubgroup`. The canonical `N → P` is the geometric
   unipotent radical: it is the radical both over `F` and after base
   change to an algebraic closure. The Levi predicate includes connected
   reductivity of `M` and an isomorphism of schemes obtained by multiplying
   `M` with a geometric unipotent radical.
4. The full standard Levi subgroup functor equals `torusCentralizer i`.
   The nonzero weights of the actual `T`-action on `Lie P`, expressed as
   `relativeRoots (torusToStandardParabolic ...)`, equal
   `positiveRelativeRoots i ν`. Thus the roots defining the chamber are
   tied to the actual parabolic Lie algebra. The affine structure needed
   to form these weights follows from the canonical closed immersion
   `P → G`.
5. There is an actual group scheme `D`, an inclusion `d : D → G`
   satisfying `IsDerivedSubgroup d`, and a maximal split torus
   `t₀ : T₀ → D` whose composite with `d` equals `j ≫ i`.
   Consequently `T₀` maps into the canonical `M` through
   `j ≫ torusToStandardLevi ...`; the published composition identity
   identifies its ambient map with `j ≫ i`.
6. There is a commutative group scheme `Z₀` and a map `z : Z₀ → T`
   whose composite into `G` is a split component, namely a maximal
   central split subtorus. The actual scheme multiplication map
   `T₀ × Z₀ → T` is surjective.

In item 6, surjectivity means surjectivity of the underlying scheme
morphism, using `AlgebraicGeometry.Surjective`. No assertion of surjectivity
on every test scheme's points is made. In particular, the source's
`T = T₀ Z₀` does not require a direct product or exclude a finite kernel.
The maps and maximality conditions are the existing all-test algebraic
predicates, rather than conditions on rational points alone.

The generic-cocharacter choice and comparison with the canonical standard
representatives are the formalization of the source's chosen positive
system and minimal parabolic. They are obligations in the setup predicate,
not consequences established in this module. No new alternative definition
of a parabolic, derived subgroup, relative root, or split component is
introduced.

## Ordered products and coverage

`C : CompactFactors F G N M` supplies compact subsets
`ΩN ⊆ N(A_F)` and `ΩM ⊆ M(A_F)¹`, and an actual compact subgroup
`K ⊆ G(A_F)`, all with their existing topologies.
For a positive threshold `t : ℝ≥0ˣ`, `IsSiegelCover ... C t` requires:

- `K` is maximal among compact subgroups and `P(A_F) K = G(A_F)`;
- `G(F) · (ΩN ΩM A_T₀(t) K) = G(A_F)¹`.

The second equality is an equality of subsets of the actual adelic point
group. The rational subgroup is the image of the existing principal map,
and the norm-one subgroup is the intersection of the kernels of the
normalized norms of all actual `F`-rational characters of `G`.
The equality includes containment of the entire rational saturation in
the norm-one group.

The product is exactly `weakSiegelProduct` with
`canonicalStandardFactors`, in the displayed order. Each simple relative
root `α` is restricted along `j` before evaluation on the intrinsic
positive subgroup of `T₀`. Its inequality is
`t ≤ normCharacter F T₀ (j ≫ α) a`.
The norm is the existing normalized idele norm, with exponent one at real
places and two at complex places. Since these positive points have finite
components equal to one, this is the source's product of archimedean
absolute values. In any splitting coordinates its value is the positive
character monomial raised to `[F : ℚ]`, as proved in
`PositiveRealTorus.normCharacter_fullIntrinsic` in `RelativeRootChamber`.
The inequalities are weak; no strict chamber from another convention is
substituted.

## Unconditional target and remaining work

`AdelicSiegelReductionStatement` quantifies over every number field and
connected reductive group scheme over that field. Explicit affine and
locally finite type interfaces supply the finite-type setting used here;
they do not contain any reduction or analytic conclusions.
The conclusion asserts existence of `T`, `i`, `ν`, `T₀`, `j` satisfying
the algebraic setup and then of `C` and `t` satisfying the coverage
predicate. All required derived and central split torus data in the setup
are also existential conclusions. No setup-existence, maximal-compact,
Iwasawa, character-triviality, or coverage hypothesis is assumed.
Empty relative-root systems and split rank zero are allowed.

The geometric comparisons, local and adelic Iwasawa theorems, and
reduction theorem remain proof obligations. Existing standard-factor
containment, conditional derived-to-norm-one maps, and Iwasawa proposition
targets do not prove this target. This module does not assert finite
volume, a measure normalization, an analytic Haar-modulus comparison,
or a comparison of the split-centre quotient with its norm-one model.

## Sources and conventions

Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
registered as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`:
§2.7, printed pp.71–72, Theorem 2.7.1, the setup preceding (2.25),
equations (2.25)–(2.26), and Theorem 2.7.2. The original pages were read
and their formulas inspected. The setup identifies the nonzero `T`-weights
on `Lie P` with the positive roots, chooses `T₀` in the derived group and
the central split torus `Z₀`, and uses `T = T₀ Z₀`. The statement here
keeps the connected number-field part of the source's scope and makes
the comparisons with canonical subgroup representatives explicit.
The rational subgroup acts on the left. The source notes after
Theorem 2.7.2 that inversion changes the root inequality when converting
the cited reduction theorem's right action to this convention.

The registered October 2026 author errata,
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read in full; it makes no correction to §2.7.
Mœglin–Waldspurger I.2.1 uses strict based chambers and a different
general-parabolic formulation. Those are not identified with the weak
chamber used here.
