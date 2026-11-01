# Cyclic monomial outputs of Fourier-regular matrix tests

This derived helper uses the canonical topology and normalized determinant
absolute value of every `PadicField.{uF} p`, for any prime `p`. The representation
carrier has its independent universe `uV`, an additive commutative group and a
complex module structure; no topology on that carrier is required. The additive
character is the supplied continuous nontrivial unitary character, and the
additive Haar measure is the supplied measure with its self-duality proof.

`fourierRegularMonomialOutputs F ρ hρ ψ ν hsd v` is a set of vectors `u`
on one fixed input `v`. Membership means that there exist an actual
Fourier-regular full-matrix test `Φ` and one integer `k` such that, for every
complex exponent `s`, its actual regular matrix zeta operator sends `v` to
`spectralPoint(q,s)^k • u`. Here `q` is the canonical residue cardinality.
Fourier regularity means that both the test and its actual plus Fourier
transform vanish on singular matrices.

`weightedRegularMatrixTest_leftTranslate` identifies the weighted group test
of `Φ(a⁻¹ X)` with the determinant weight of `a` times the ordinary left
translate of the original weighted group test. The published integrated Hecke
action therefore gives `regularMatrixZetaOperator_leftTranslate`: its output
is the determinant weight times `ρ(a)` applied to the original output. These
two identities hold for every smooth representation and every rank `n+1`.

`regularMatrixZetaOperator_eq_of_detNorm_support` shows that a regular test
supported on determinant norm one gives an operator independent of `s`.
For `m > 0` and a supercuspidal representation of rank `m+1`,
`exists_fourierRegular_constant_output_of_pairing` applies this fact to the
conjugate of the existing coefficient cutoff. For a smooth functional `ℓ`
with `ℓ(v) ≠ 0`, evaluating the resulting operator gives the integral of the
squared norm of that cutoff. This integral is strictly positive: the cutoff
is continuous with compact support and has nonzero value `ℓ(v)` at the
identity. The output is consequently a single nonzero vector for all `s`.
`exists_fourierRegular_constant_output` obtains the required smooth functional
from the proved smooth-dual separation lemma for every nonzero input `v`.

`representation_mem_fourierRegularMonomialOutputs` translates a realizing
test by `a⁻¹` on the left. Fourier regularity is preserved by the published
translation map, and the actual determinant weight is the spectral power with
exponent `ord(det(a))`. Thus `ρ(a)u` is again a monomial output, with exponent
`ord(det(a)) + k`. Finally,
`span_fourierRegularMonomialOutputs_eq_top` assumes irreducibility in addition
to supercuspidality and `m > 0`. A nonzero constant output belongs to the set
with exponent zero; the set contains its entire representation orbit, whose
complex span is the whole carrier by `span_range_orbit_eq_top`.

The provenance is internal: the construction combines the existing conjugate
coefficient cutoff and its Fourier regularity, the actual integrated zeta
operator, smooth-dual separation, invertible Fourier-regular translations,
the normalized determinant-weight identity and irreducible orbit spanning.
This helper establishes output spanning. A functional equation, scalar
comparison and extension to arbitrary matrix tests remain separate results.
