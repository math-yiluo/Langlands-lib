# Proof of the centralizer coset property at unit discriminant

`Langlands.TraceFormula.unitDiscriminantCentralizerCoset` proves
`Langlands.TraceFormula.UnitDiscriminantCentralizerCosetStatement` at its universe
parameter `u`. [Published statement](UnitDiscriminantCosetStatement.md).

Let `O` be a valuation subring of a field `F`, write `ι : O → F` for the inclusion
`O.subtype` and `GL_n(O)` for `Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring`.
Let `γ ∈ GL_n(O)` with `O.valuation (charpoly γ).discr = 1`, and let `x ∈ GL_n(F)` with
`δ := x⁻¹ * γ * x ∈ GL_n(O)`.

## Proof

**Integral matrices.** The entries of `γ` and of `δ` lie in `O`, so they define matrices
`A` and `B` over `O` with `A.map ι = γ` and `B.map ι = δ`. Conjugation does not change the
characteristic polynomial over `F` (`Matrix.charpoly_units_conj'`), and `Matrix.charpoly_map`
together with injectivity of `ι` on polynomial coefficients gives
`A.charpoly = B.charpoly` over `O`.

**Separability over `O`** (`separable_charpoly_of_valuation_discr_eq_one`). Let
`p = A.charpoly`, a monic polynomial over `O`. If `deg p = 0` then `p = 1`, which is
separable. Otherwise let `r` be the resultant of `p` and `p'` with the Sylvester sizes
`deg p` and `deg p - 1`. The image of `r` in `F` is the same resultant of `p.map ι` and its
derivative (`Polynomial.resultant_map_map`, `Polynomial.derivative_map`; `p.map ι` is monic of
the same degree). By `Polynomial.resultant_deriv` this resultant equals
`(-1)^(d(d-1)/2) · disc(p.map ι)` with `d = deg p`, the leading coefficient being `1`.
Since `p.map ι = charpoly γ`, the valuation of `ι r` is `1`, so `r` is a unit of `O`
(`ValuationSubring.valuation_eq_one_iff`). `Polynomial.exists_mul_add_mul_eq_C_resultant`
gives `p · a + p' · b = r` over `O`; multiplying by `r⁻¹` gives a Bézout identity, so `p` is
separable over `O` (`separable_of_isUnit_resultant_derivative`).

**Integral conjugacy** (`exists_units_conj_of_charpoly_separable`). Over any local ring `R`,
let `A` and `B` have the same characteristic polynomial, separable over `R`. Its reduction to
the residue field is separable (`Polynomial.Separable.map` and `Matrix.charpoly_map`). By
`Langlands.BaseChange.regularCyclicBasis` the reduced matrix has a cyclic vector, i.e. a
vector `v₀` with invertible cyclic-basis matrix `[v₀, A v₀, …, A^(n-1) v₀]`. Lift `v₀`
coordinatewise to `v` over `R`. By `Langlands.BaseChange.cyclicBasisMatrix_map` the reduction
of the cyclic-basis matrix of `v` is that of `v₀`, so its determinant has nonzero residue and
is a unit of `R` (`exists_isUnit_cyclicBasisMatrix_of_residue`). Doing the same for `B`, the
two invertible cyclic-basis matrices `P_A` and `P_B` give `z₀ = P_A · P_B⁻¹ ∈ GL_n(R)` with
`A · z₀ = z₀ · B`, by `Langlands.BaseChange.cyclicBasis_conjugator`, which uses the common
characteristic polynomial.

**Coset decomposition.** Applied to `R = O`, this gives `z₀ ∈ GL_n(O)` with `A z₀ = z₀ B`.
Its image `z = Matrix.GeneralLinearGroup.map ι z₀` has entries of `z` and `z⁻¹` in `O`, so
`z ∈ GL_n(O)`, and applying `ι` entrywise gives `γ z = z δ`, i.e.
`x⁻¹ γ x = z⁻¹ γ z`. Put `c = x z⁻¹` and `k = z`. Then `x = c k`, and

`γ c = x (x⁻¹ γ x) z⁻¹ = x (z⁻¹ γ z) z⁻¹ = c γ`,

so `c ∈ Subgroup.centralizer {γ}` (`Subgroup.mem_centralizer_iff`).

The argument uses only that the valuation subring `O` is a local ring; the
`IsDiscreteValuationRing O` hypothesis of the statement is not used.

## Auxiliary results

The module also proves, in the namespace `Langlands.TraceFormula`:

- `separable_of_isUnit_resultant_derivative`: over a commutative ring, a polynomial `p` of
  positive degree is separable when the resultant of `p` and `p'` with sizes `deg p` and
  `deg p - 1` is a unit.
- `exists_isUnit_cyclicBasisMatrix_of_residue`: over a local ring, a square matrix whose
  reduced characteristic polynomial is separable has a vector with invertible cyclic-basis
  matrix.
- `exists_units_conj_of_charpoly_separable`: over a local ring, two square matrices with the
  same separable characteristic polynomial satisfy `A * z = z * B` for some `z ∈ GL_n(R)`.
- `separable_charpoly_of_valuation_discr_eq_one`: for a matrix `A` over a valuation subring
  `O` of `F`, if the discriminant of the characteristic polynomial of `A.map O.subtype` has
  valuation `1`, then `A.charpoly` is separable over `O`.

The residue-lifting step and the integral conjugator follow the same argument as the finite
places in `Langlands/TraceFormula/AdelicRegularConjugacy.lean`, there with the Bézout identity
obtained from a global one rather than from the discriminant.

## Connection to the good-place coset calculation

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma 17.8.3 and its
proof (printed pp. 464–465), use properness of the orbit map (Theorem 17.7.1) and
Exercise 17.15 (printed p. 470): after enlarging the finite set of places `S'`, the inverse
image of `X(Ô_F^{S'})` in `H_γ(A_F^{S'})\H(A_F^{S'})` corresponds under (17.56) to the
restricted product of the sets `H_γ(F_v) K_v` for `v ∉ S'`. At a single place `v`, for the
conjugation action of `GL_n` on itself with orbit map `x ↦ x⁻¹ γ x` as in the statement and
`K_v = GL_n(O_v)`, the stabilizer `H_γ(F_v)` is the centralizer of `γ`, and this says that
every `x` with `x⁻¹ γ x ∈ GL_n(O_v)` lies in `Z(γ) · GL_n(O_v)`.

The theorem proved here gives that conclusion at every place `v` where `γ ∈ GL_n(O_v)` and
the discriminant of the characteristic polynomial of `γ` is a `v`-adic unit, without the
properness argument. For `γ ∈ GL_n(F)` with separable characteristic polynomial over a
global field `F`, the discriminant is a nonzero element of `F`, so both conditions hold at
all but finitely many places; this module does not formalize that finiteness. The remaining
step of Lemma 17.8.3, `RO_γ(1_{X(O_{F_v})}) = 1`, also uses the measure normalization
`K_{γ,v} = K_v ∩ H_γ(F_v)` and the triviality of `χ` on `K_v`; this module does not treat it.
[Getz–Hahn (2024)](https://link.springer.com/book/10.1007/978-3-031-41153-3)
