# Coefficient growth on the Levi scheme and the actual Levi subgroup

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927`, revision 1.

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviTempered`.
All declarations below are in `Langlands.HarishChandraSchwartz`.

## Provenance and source convention

This is an internal derived comparison between the Library's two realizations of a standard
Levi group, using the canonical `SmoothRep` interface. The recorded construction is
`leviSchemeRepresentation`, the same-carrier pullback of a smooth representation of the actual
subgroup along `leviSchemePointsEquiv`. It is not a separate representation framework.

The source convention is J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`.
The original PDF pages 6, 18 and 31 (printed pages 240, 252 and 265) were read. In I.1 Waldspurger
uses `M ∩ K` for the Levi compact subgroup; in II.1 he constructs `Ξ^M` by applying the group
construction to `M`; in III.2 he defines tempered representations by growth bounds for all their
smooth-dual coefficients. The present module makes that compatibility explicit for the existing
rational-point objects; the comparison theorem is derived here rather than attributed to a
separately numbered result in the article.

The pure Xi comparison extends this same pullback construction using the existing
`HasXiBoundedCoefficients` predicate from `OrbitCoefficientBound`. Waldspurger's proof of
Lemma VI.2.2, printed pages 298–299 (PDF pages 64–65, read in the original), uses coefficient
bounds by `c Ξ^M` on a Levi in estimating unitary twists of induced representations. The
transport result here is an internal compatibility lemma for that predicate. It asserts no
new analytic coefficient estimate.

## Generic coefficient transport

For groups `G` and `H` with topologies, an arbitrary complex representation `ρ` of `G` on `V`,
a topological group isomorphism `e : H ≃ₜ* G`, and an arbitrary real weight `Ξ` on `G`,
`hasXiBoundedCoefficients_comp_continuousMulEquiv_iff` proves

`HasXiBoundedCoefficients (Ξ ∘ e) (ρ.comp e.toMonoidHom)` if and only if
`HasXiBoundedCoefficients Ξ ρ`.

Here the bound is `‖ℓ(ρ(g)v)‖ ≤ c Ξ(g)`, for all `g`, with a positive real `c` for each pair
`(v, ℓ)` and `ℓ` in the smooth algebraic dual. The constant is unchanged by transport.

With an additional arbitrary real weight `σ` on `G`,
`hasTemperedCoefficients_comp_continuousMulEquiv_iff` proves

`HasTemperedCoefficients (Ξ ∘ e) (σ ∘ e) (ρ.comp e.toMonoidHom)` if and only if
`HasTemperedCoefficients Ξ σ ρ`.

There are no smoothness, admissibility, positivity, local compactness or measure hypotheses for
these generic theorems. The group and vector-space universes are independent. Each proof uses
`isSmoothVector_dual_comp_continuousMulEquiv_iff` to identify the same algebraic functionals as
smooth in both actions. In one direction it evaluates the coefficient bound at `e.symm g`;
in the other it evaluates at `e h`. For temperedness the same constants and exponents work.

## Levi construction and comparison

Let `F` be a nonarchimedean local field in any characteristic, `G` an affine group scheme locally
of finite type over `F`, `S` a commutative group scheme, `i : S → G`, `ν` a cocharacter and `J`
a set of characters. Write `L = Standard.leviScheme i ν J` and `j = Standard.leviHom i ν J`.
Rational points have the canonical topology from `RationalWeights`.

- `leviSchemeRepresentation i ν J A` is `SmoothRep.pullback (leviSchemePointsEquiv i ν J) A`
  for a smooth complex representation `A` of `standardLeviPoints i ν J`. Its vector-space carrier
  and linear maps are unchanged. `leviSchemeRepresentation_apply` gives the action explicitly:
  `x` acts as `A(j(x))`.
- `hasXiBoundedCoefficients_leviSchemeRepresentation_iff` proves that the pure Xi bound for this
  representation on `L(F)`, with the Xi function defined using the compact `j⁻¹(K)` and the
  transported minimal parabolic, holds if and only if the pure
  `rationalLeviXi hKc hM` bound holds for `A` on the actual subgroup. No matrix representation or
  height enters this comparison.
- `isRationalTempered_leviSchemeRepresentation_iff` proves that this representation is
  `IsRationalTempered` for the compact subgroup `j⁻¹(K)` and the restricted matrix representation
  `ρ.restrict j` if and only if `A` is `IsRationalLeviTempered` for `K ∩ M_J(F)` and `σ_ρ|_M`.

Both comparisons assume connected reductivity of `G`, maximal splitness of `i`, genericity of `ν`,
`J ⊆ simpleRelativeRoots i ν`, a compact open subgroup `K` of `G(F)`, and the displayed Levi
Iwasawa decomposition

`hM : M_J(F) = (P₀(F) ∩ M_J(F)) (K ∩ M_J(F))`.

The temperedness comparison accepts any matrix representation
`ρ : MatrixRepresentation G (Fin N)` with nonempty index set. Closedness of `ρ` and
admissibility of `A` are unnecessary for these coefficient comparisons.
For admissible `A`, the tempered coefficient predicate is the Library's reading of Waldspurger's
`A(π) ⊆ A_w(G)`.

The pure Xi comparison rewrites the weight by the published `rationalXi_leviScheme` and applies
its generic transport theorem. The temperedness proof also rewrites the height by
`rationalHeight_restrict_leviHom` and applies the generic temperedness theorem. The Levi Iwasawa pair
is the published `isIwasawaPair_leviSchemeCompact hG hi hν hJ hM`; openness and compactness of its
compact subgroup come from `isOpen_leviSchemeCompact` and `isCompact_leviSchemeCompact`.
The needed affine and finite-type instances for `L` come from `leviScheme_isAffineHom` and
`leviScheme_locallyOfFiniteType`.

## Scope and remaining obligations

The results transport a coefficient bound that holds on either realization. They prove no new
representation tempered or Xi bounded, and assume the explicit Levi Iwasawa decomposition `hM`; its
existence is a separate structural obligation. No Xi upper bound, square-weight integrability,
discrete-series estimate, measure comparison or Plancherel conclusion is assumed or proved here.
The representation carrier may live in any universe, independently of the local field. In
particular the pure Xi result can supply the `hcoeff` premise used by the actual Levi
coefficient and unitary-orbit constructions when the corresponding bound on `L(F)` is supplied.
The discrete-series decay theorem and the passage from decay on the source's `G¹` to the
whole-group bound remain separate obligations.
