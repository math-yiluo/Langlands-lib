# Actual normalized-section Jacquet evaluation

This module is an internal derivation connecting the actual normalized compact
sections in `AdjacentRankNormalizedSection` to the convergent scalar integral
comparison in `AdjacentRankDoubleIntegral`. It supplies the pure-section
evaluation step needed for the adjacent-rank image theorem. The definitions
and proofs use those modules' actual algebraic averages, canonical induction,
Haar measures, determinant weights and Fourier equivalence.

Fix a prime, the canonical data of a p-adic field `F`, any natural `r`, an
original complex module `V` and a representation `σ` of `GL_(r+1)` on `V`.
The field and module universes are independent. No topology or norm is placed
on `V`, and its coefficient map need not be injective. Let `ℓ` be a specified
standard Whittaker functional, and let `χ` be an arbitrary continuous
quasicharacter. The notation `|det|` below means the canonical normalized
absolute value.

`AdjacentJacquet.upperColumn x` is the actual element
`u(x)=[I,x;0,1]` of `GL_(r+2)`, implemented by `Shahidi.upper`. Its four
block-entry theorems fix the last-coordinate convention. Its determinant is
one, proved by reindexing to a triangular block matrix, and
`rectangularJoin_mul_upperColumn` proves the literal identity

`[A,0] u(x) = [A,Ax]`.

Write
`θ(g)=χ(det g)|det g|^((r+1)/2)` and
`ξ(h)=χ(det h)|det h|^((r+2)/2)`.
`determinantWeight_eq` identifies the smooth unit-valued determinant character
of the section construction with the complex scalar weight used in the
integral model.

The selected definition `sectionCoefficient f g` evaluates an actual vector
of the canonical normalized lower-parabolic induction at `g`, applies
`adjacentRankLowerTensorCoordinates` to its original tensor carrier, and then
applies `ℓ`. Its companion `integrand f g x` is

`sectionCoefficient f (u(x)g) ψ(-x_last)`.

For the pure normalized compact section `s(Φ,v)`, the test `Φ` belongs to
`adjacentRankCompactTests`: it is a rectangular Schwartz–Bruhat function
whose entire topological support lies in the full-row-rank locus.
`sectionCoefficient_normalizedSection` proves

`sectionCoefficient s(Φ,v) g =
 θ(g) ∫_h Φ([h,0]g) ξ(h) ℓ(σ(h⁻¹)v) dh`.

The measure `dh` is exactly `generalLinearHaar F.Carrier r`. This is a
consequence of the normalized-section evaluation formula, the pair-tensor
coordinate identity and `adjacentRankCompactAverage_dual`: applying the
algebraic dual to the finite algebraic average gives the scalar Bochner
integral. It does not require integration in the original module.
Only smoothness of `σ` is needed for this formula.

`integrand_normalizedSection` uses `det u(x)=1`, the rectangular identity,
and commutativity of the scalar factors to obtain

`integrand s(Φ,v) g x =
 θ(g) ∫_h (R_g Φ)([h,hx]) W_v(h⁻¹)
            χ(det h)|det h|^((r+2)/2) ψ(-x_last) dh`,

where `W_v=modelMap σ ℓ v` and `R_g Φ(M)=Φ(Mg)`. The inner expression is
literally `AdjacentDoubleIntegral.integrand`, so its character sign, last
coordinate and determinant exponents are unchanged.
`integral_normalizedSection_eq_doubleIntegral` integrates this identity and
factors out `θ(g)` using the scalar Bochner integral. This algebraic identity
holds for every continuous `χ`; convergence is proved separately below.

Now assume the target's full `IsOfWhittakerType` predicate on `σ`. For any
continuous base character `χ₀`, put
`χ_u=AdjacentCompactMatrix.realTwistedCharacter F χ₀ u`. If
`realTwistThreshold F ψ σ hσ ℓ χ₀ < u`, then
`integrable_normalizedSection_realTwist` proves actual scalar `Integrable`
of the displayed Jacquet kernel against `rowMeasure ν (r+1)` for every
pure normalized compact section and every ambient `g`. It applies the
proved product integrability in `AdjacentDoubleIntegral` to `R_g Φ` and
`W_v`, takes its integral in `h`, multiplies by the constant `θ(g)` and
uses the pointwise identity. The same threshold precedes `u`, `Φ`, `v`
and `g`. No convergence premise is added.

For the supplied scalar additive Haar `ν` and a certificate that it is
self-dual for `ψ`, `integral_normalizedSection_eq_modelIntegral` proves
for every `g` that

`∫_x integrand s(Φ,v) g x dx =
 adjacentRankModelIntegral
   ((partialFourierEquiv ψ ν (r+1) hself Φ) ⊗ W_v) g`.

The model integral uses `χ_u`, the canonical absolute value and the same
normalized GL Haar. The proof is the preceding double-integral identity
followed by `AdjacentDoubleIntegral.double_integral_eq_modelIntegral`,
which already proves the column change of variables, absolute convergence,
Fubini and inverse-character partial-Fourier comparison.

All ranks, including `r=0`, are retained. The functional `ℓ` may be zero
in these evaluation lemmas; no irreducibility or extra analytic premise is
used. These results identify and prove convergence on pure compact sections.
Spanning the whole induction, defining a common induced Whittaker functional,
proving its nonvanishing and proving the whole image equality remain separate
obligations.
