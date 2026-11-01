# Concrete cone majorant for the lower integrand

This internal derived module combines the separately established block-section,
coefficient, Fourier and diagonal-density bounds for the actual Section 4.7
lower integrand. Its provenance is the imported coordinate, growth, support,
geometric-summability and compact partial Fourier results. It proves a summable
bound in standard torus coordinates, retaining the canonical p-adic field,
the supplied unitary additive character and self-dual Fourier Haar measure.
It does not itself assert quotient integrability.

Write `q` for the residue cardinality, `size lam` for the sum of the absolute
integer exponents and `s = Iic j.castSucc`, where `j.val = m 1`. The signed
degree is `sum i in s, lam i - sum i in sᶜ, lam i`. The inclusive cut puts
the rotated second block in `s`.

`blockRotation_inv_mul_torus` moves the inverse block rotation through the
canonical torus by the inverse permutation. `exists_rotated_section_growth`
then applies the block-section growth estimate at the permuted torus and the
integral compact factor `blockRotation⁻¹ * k`. The permutation preserves
`size`. The inverse block half modulus is bounded by
`(q ^ ((m 0 + 1) * (m 1 + 1))) ^ size lam`, and is absorbed into a fixed
base `Bs ≥ 1`. The opposing determinant powers remain exactly
`q ^ (-u * degree lam)`. For every real `u` and every section of the actual
opposite-twist representation, the section factor is therefore bounded by
`Cs * Bs ^ size lam * q ^ (-u * degree lam)` on the integral compact
subgroup. `Bs` is chosen before `u` and the section; `Cs ≥ 0` may depend
on both. Both blocks have the supplied full Whittaker type, and their supplied
inverse functionals, including zero, are used after transport by the twist.

`integrand_standard_mk` computes the exact descended integrand at the inverse
image of the standard class of `g`. It is the product of the supplied test
Whittaker function at `g`, the scalar section at `blockRotation⁻¹ * g`,
and the supplied partial Fourier factor at that same rotated representative.
In particular, the test function has no left rotation.

`exists_integrand_torus_majorant` assumes a test representation of full
Whittaker type, its supplied functional, and the preceding block data. The
coefficient estimate contributes a fixed base `Bw ≥ 1`, and the compact
partial Fourier estimate contributes the base `q`. Their product
`B = Bw * Bs * q ≥ 1` is chosen before `u`, the section, the actual
coefficient-image vector and the row Schwartz function. For all such later
data, one `K ≥ 0` bounds the integrand norm by
`K * B ^ size lam * q ^ (-u * degree lam)` for every integer exponent
vector and every integral compact factor.

The same theorem confines every nonzero value to `OppositeCone M s`.
Smoothness of the test coefficient bounds consecutive root differences by
some natural `L`. The Fourier factor bounds the two exponents bordering
the cut from opposite sides by a natural cutoff. Propagating these endpoint
bounds along the bounded differences yields a common natural `M`. These
support constants may depend on the later test data; they do not enter `B`.
No irreducibility, functional equation, multiplicativity, or outer convergence
assumption is used.

`coneMajorant s K B q u M lam` is the displayed bound on `OppositeCone M s`
and zero elsewhere. It is nonnegative when `K`, `B` and `q` are nonnegative.
The explicit inverse Borel diagonal density is nonnegative as well.

Finally, `exists_summable_integrand_majorant` sets
`D = q ^ (2 * (t + 1) * (t + 1)) ≥ 1`, the fixed density growth base.
It chooses a real threshold `C` for which `u > C` implies `u ≥ 0` and
`D * B * q ^ (-u) < 1`. This choice precedes `u`, every section,
coefficient-image vector and row Schwartz function. For all those later
inputs, the theorem supplies a nonnegative real function `A lam` bounding
the norm of the exact integrand uniformly over the integral compact factor.
The product `diagonalDensity F lam * A lam` is summable over the entire
integer lattice. Indeed the density is at most `D ^ size lam`, and the
product is bounded by `K` times the cone-supported geometric-twist series
with base `D * B`. The imported cone summability theorem applies with the
chosen ratio. The amplitude and cone cutoff may vary with the later inputs,
while the threshold remains fixed. This result is independent of the quotient
measure and of any determinant-slice integer.
