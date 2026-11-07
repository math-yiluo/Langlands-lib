# Ordered spherical cyclicity and the normalized inverse Whittaker realization

This module states two assertions for the actual normalized unramified principal
series constructed in
[`UnramifiedPrincipalSeries`](UnramifiedPrincipalSeries.md). They are
Prop-valued definitions, with no proof of either assertion. All three declarations
are in `Langlands.Conductor`:

| Declaration | Assertion |
| --- | --- |
| `OrderedUnramifiedSphericalCyclicityStatement` | Every subrepresentation containing the spherical section is the whole principal series, for every norm-ordered tuple. |
| `OrderedUnramifiedWhittakerRealizationStatement` | There is a nonzero inverse-character functional with injective coefficient map whose spherical image is exactly the explicit spherical Whittaker function. |
| `OrderedUnramifiedWhittakerStatement` | The conjunction of these two universal assertions at the same arbitrary field universe `uF`. |

## Actual objects and scope

Each individual statement quantifies over every `F : Type uF`, with `Field F`,
`ValuativeRel F`, its given `TopologicalSpace F`, and
`IsNonarchimedeanLocalField F`. The field universe is arbitrary. Positive
characteristic is included, and there is no p-adic-field or characteristic-zero
specialization.

The remaining explicit arguments, in order, are `ϖ : Fˣ`,
`hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ`, `n q : ℕ`,
`hq : UnramifiedPrincipalSeries.IsResidueCardinality (F := F) q`, and
`z : Fin (n + 1) → ℂˣ`. Here `ℂˣ` means all nonzero complex numbers, with no
modulus-one restriction. Positive rank is `n + 1`, so rank one is included.
The witness `hq` ties `q` to the cardinality of the actual residue field of
`(ValuativeRel.valuation F).integer`.

Write `ρ = UnramifiedPrincipalSeries.principalSeries hϖ n hq z` and
`f₀ = UnramifiedPrincipalSeries.sphericalSection hϖ n hq z`.
These are the imported actual representation and vector. Its carrier is
`UnramifiedPrincipalSeries.PrincipalSeries hϖ n hq z`, consisting of uniformly
right-smooth complex-valued functions on `GL_(n+1)(F)` with upper-Borel
covariance. With `χ_i(ϖ) = z_i` and `χ_i` trivial on valuation units, the
conventions are

\[
 f(bg)=\delta_B^{1/2}(b)\prod_i\chi_i(b_{ii})f(g),
 \qquad (\rho(g)f)(x)=f(xg).
\]

Thus induction is normalized for the upper Borel and the action is right
translation. The positive square-root half modulus is the one explicitly
constructed from the actual residue cardinality in the imported module.
The section `f₀` equals one on `GL_(n+1)(O)` and is invariant under that group
on the right.

## Ordering and cyclicity

Both assertions have exactly the ordering hypothesis
`Monotone (fun i => ‖(z i : ℂ)‖)`. In one-based notation this says
`|z₁| ≤ ... ≤ |z_(n+1)|`. Jacquet writes `z_i = q^(-t_i)` and orders
`Re(t₁) ≥ ... ≥ Re(t_(n+1))`; because `|z_i| = q^(-Re(t_i))` and the residue
size is greater than one, these conventions give the stated increasing norm
order. The complex exponents are explanatory coordinates, not additional Lean
data or assumptions.

The first assertion then quantifies over every actual
`S : Subrepresentation ρ` and states `f₀ ∈ S → S = ⊤`. It concerns the entire
induced representation. Weak inequalities, equal norms, and reducible tuples
are included; irreducibility is not an assumption.

## Functional, coefficient map, and normalization

The second assertion additionally quantifies over each actual
`ψ : UnitaryAdditiveCharacter F` satisfying the unchanged
`Langlands.Conductor.HasIntegerConductor ψ`. This means that `ψ` is trivial
on `O` and its annihilator of `O` is exactly `O`.

Its conclusion is an actual
`ℓ : Langlands.Whittaker.glInverseFunctionals ψ n ρ`, with all three properties
in the conclusion:

1. The underlying complex linear functional `ℓ.val` is nonzero.
2. `Langlands.Whittaker.coefficientMap ρ ℓ` is injective on the entire induced
   carrier.
3. For every actual matrix `g : Langlands.GeneralLinear (n + 1) F`,
   the value at `g` of `coefficientMap ρ ℓ f₀` is
   `Langlands.GeneralLinear.Spherical.sphericalWhittaker hϖ
   (Langlands.Whittaker.inverseStandardCharacter ψ n) q z g`.

The coefficient map is the imported intertwiner `f ↦ (g ↦ ℓ(ρ(g)f))`.
Its values lie in the actual space of functions equivariant for
`inverseStandardCharacter ψ n` under left multiplication by the upper
unipotent subgroup. This is the convention for the second member of a
Rankin–Selberg pair: for a unitary additive character, complex conjugation of
`ψ` is its pointwise inverse. The right-hand side is the existing explicit
spherical Whittaker function, given by the half modulus times the Satake
Schur function on dominant torus cells, with the inverse-character unipotent
factor. Equality is pointwise at every matrix, rather than only on the torus
or up to a scalar.

## Original source and provenance

The registered original source is H. Jacquet, *A correction to Conducteur des
représentations du groupe linéaire*, Pacific Journal of Mathematics 260
(2012), 515–525, DOI
[10.2140/pjm.2012.260.515](https://doi.org/10.2140/pjm.2012.260.515),
literature ID `jacquet-2012-conductor-correction`. The retained central PDF
has SHA256
`98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.
No project erratum file `notes/errata/jacquet-2012-conductor-correction.md`
was present when preparing this statement.

Printed p. 515 fixes an arbitrary nonarchimedean local field, its residue
cardinality and a character of conductor `O`. Printed p. 516 specifies the
normalized upper-triangular covariance and spherical section, as well as the
normalized spherical Whittaker function. Section 1 starts on printed p. 517
with the decreasing real-part ordering. On printed p. 518:

- Lemma 1 states cyclicity of the spherical section with this ordering.
- The paragraph before Lemma 2 supplies a nonzero functional for the inverse
  character `θ_(r-1,bar ψ)`. Lemma 2, attributed there to Jacquet–Shalika
  (1983), states injectivity of the resulting coefficient map.
- The paragraph following Lemma 2 identifies the image of the spherical
  section with the normalized spherical Whittaker function up to a scalar.

The exact normalization in the second Lean assertion packages this final
comparison by rescaling the functional. If its spherical image is
`c W_sph`, injectivity and `f₀ ≠ 0` force `c ≠ 0`; replacing the functional by
`c⁻¹ ℓ` preserves its inverse-character law, nonvanishing and injectivity,
and gives image `W_sph`. This is the mathematical derivation of the requested
normalization from Jacquet's comparison; no such rescaling proof is implemented
here. The convention is already inverse-character on Jacquet's printed p. 518.
The assertion uses the existing explicit Schur-formula realization of his
normalized spherical function, so its comparison with that explicit formula
is part of the subsequent proof obligation.

The module introduces no cyclicity, functional, injectivity, spherical
comparison, essential identity, factor comparison or conductor conclusion as
a premise. Proving these two assertions, the principal-series pair-factor
identity, and the essential-vector and conductor theorem are subsequent work.
The imported principal-series construction, `Essential`, `EssentialStatement`,
and their imported files are unchanged.
