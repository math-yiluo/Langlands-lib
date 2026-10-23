# Lifting property of compact irreducible admissible representations

This internal module proves that an irreducible admissible complex
representation `ρ` with compact smooth-dual coefficients is projective among
smooth representations. Every intertwiner from `ρ` to the target of a surjective
intertwiner of smooth representations lifts through it. In particular, every
surjection onto `ρ` has an equivariant section. All declarations are in namespace
`Langlands.CompactSplitting`.

The group `G` is a topological group. In the integration sections it also has a
Borel measurable structure. The carriers `V`, `W`, `U` are complex vector spaces
without topology. Their universes and the group universe are independent. The
measure `μ` is a left Haar measure (`Measure.IsHaarMeasure`); the proof uses no
right invariance or unimodularity. Where needed, the hypothesis `hcof` states
that every open subgroup contains a compact open subgroup.

## Coefficients and test functions

For a representation `ρ`, an algebraic functional `ℓ` and a vector `v`,
`invCoeff ρ ℓ v` is the function `x ↦ ℓ (ρ x⁻¹ v)`. For smooth `ρ` it is
locally constant, because it is the published locally constant orbit map composed
with `ℓ` and inversion. If `ρ` has compact smooth-dual coefficients and `ℓ` is a
smooth vector of the algebraic dual action `ρ.dual`, it has compact support,
because it is the compactly supported coefficient `x ↦ ℓ (ρ x v)` composed with
the inversion homeomorphism.

`testMap ρ hρ hc ℓ hℓ` packages these functions as a complex-linear map from `V`
to the project's test functions `SchwartzBruhat G`.
`testMap_translate` records the identity

`testMap (ρ g w) = leftTranslate g (testMap w)`,

which follows from `(g⁻¹ x)⁻¹ = x⁻¹ g`.

## The integrated map and the Hermitian form

`liftMap μ ρ hρ hc ℓ hℓ σ hσ a` is the actual intertwiner from `ρ` to a smooth
representation `σ` given by

`w ↦ ∫ ℓ (ρ x⁻¹ w) σ(x) a dμ(x)`.

It is computed by the published integrated Hecke action
`Hecke.integratedAction μ σ hσ`. It is linear because the Hecke action is linear
in the test function. It is equivariant by `testMap_translate` and the published
`Hecke.integratedAction_leftTranslate`. `liftMap_natural` applies the published
`Hecke.integratedAction_intertwiner`: for an intertwiner `p : σ → τ` of smooth
representations, `p (liftMap … σ … a w) = liftMap … τ … (p a) w`.

`form μ ρ ℓ v w` is the integral

`∫ ℓ (ρ x⁻¹ v) · conj (ℓ (ρ x⁻¹ w)) dμ(x)`.

The integrand is continuous with compact support, hence integrable, when `μ` is
finite on compacts (`form_integrable`). `formLeft` is the resulting linear
functional `v ↦ form μ ρ ℓ v w`. The form has the following properties:

- `form_invariant`: `form (ρ g v) (ρ g w) = form v w`. This is left invariance
  of `μ`, via `integral_mul_left_eq_self`.
- `form_conj`: `conj (form v w) = form w v`.
- `form_self_ne_zero`: `form v v ≠ 0` when `ℓ v ≠ 0` and `μ` is positive on
  open sets. It applies `integral_mul_conj_ne_zero`: the integral of
  `|F|²` for a continuous compactly supported `F` that is nonzero at a point is
  a positive real number.
- `formLeft_isSmoothVector`: each `formLeft … v` is a smooth vector of
  `ρ.dual`. It is fixed by any open subgroup fixing `v`, by invariance of the
  form.

## Lifting

`exists_smooth_functional_ne_zero hcof ρ hρ hv` shows the following. If
compact open subgroups are cofinal, every nonzero vector `v` of a smooth
representation has a smooth functional `ℓ` with `ℓ v ≠ 0`. This is
injectivity of the published smooth bidual map,
`smoothBidual_injective_of_compact_cofinal`. Only smoothness is assumed here.

`exists_lift μ hcof ρ hρ hirr hc hσ hτ p hp φ` takes the following data.

- `ρ` is admissible (`hρ : IsAdmissible ρ`), irreducible and has compact
  smooth-dual coefficients.
- `p : σ → τ` is a surjective intertwiner of smooth representations.
- `φ : ρ → τ` is an intertwiner.

It produces `s : ρ → σ` with `p.comp s = φ`. The proof proceeds as follows.

1. Choose `v₀ ≠ 0` and a smooth `ℓ₀` with `ℓ₀ v₀ ≠ 0`. Put
   `ℓB = form(·, v₀)` for the form built from `ℓ₀`. Then `ℓB` is smooth.
2. The endomorphism `T = liftMap … ρ … v₀` of `ρ` is a scalar `c` by the
   published admissible Schur lemma `admissibleSchur_scalarEndomorphism`.
3. `c ≠ 0`: otherwise `ℓB (T v₀) = 0`. By the published
   `Hecke.integratedAction_dual`, `ℓB (T v₀)` is the integral of
   `F(x) · conj F(x)` with `F(x) = ℓB (ρ x v₀) = form (ρ x v₀) v₀`. The
   conjugation and invariance identities of the form rewrite the test function
   as `conj F`. Moreover `F(1) = form v₀ v₀ ≠ 0`, so the integral is nonzero.
4. Choose `a₀` with `p a₀ = φ v₀` and put `s = c⁻¹ • liftMap … σ … a₀`. By
   naturality applied to `p` and to `φ`, `p (s w) = c⁻¹ • φ (T w) = φ w`.

`exists_section` is the case `τ = ρ`, `φ = id`.

## Provenance

The module is internal infrastructure for the analytic complement in
`AdmissibleComplement`. Its results are standard properties of representations
with compact coefficients. Compare I. N. Bernstein and A. V. Zelevinsky,
*Representations of the group GL(n,F) where F is a non-archimedean local
field*, Russian Math. Surveys 31:3 (1976) (literature ID
`bernstein-zelevinsky-1976-representations-gln`), Sections 2.42–2.43 and
Theorem 2.44(a), pp. 27–28. There, under unimodularity and countability at
infinity, irreducible “finite” (compact-coefficient) representations split off
as direct summands. The Lean statements are not translations of those
statements. The implemented route is our own: an invariant
Hermitian form built from one compact coefficient, the admissible Schur lemma,
and a single test function. It uses no Schur orthogonality relations, formal
degrees or unimodularity.
