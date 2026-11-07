# Normalized unramified principal series over a nonarchimedean local field

This module constructs the normalized upper-Borel principal series and its
normalized spherical section as actual functions on the general linear group.
All declarations are in `Langlands.Conductor.UnramifiedPrincipalSeries`.

The source is H. Jacquet, *A correction to Conducteur des representations du
groupe lineaire*, Pacific J. Math. 260 (2012), 515–525, registered as
`jacquet-2012-conductor-correction`. Printed p. 515 fixes an arbitrary
nonarchimedean local field, its residue cardinality, and the convention
`|a| = q^(-v(a))`. Printed p. 516 gives normalized upper-triangular covariance
and the spherical section equal to one on the integral general linear group.
The source PDF has SHA256
`98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.
No project erratum for this source was found. The implementation below is an
explicit construction of those objects using existing induction and Iwasawa
interfaces; its choice functions and auxiliary homomorphisms are internal
implementation details, rather than extra results attributed to Jacquet.

## Field, parameters, and scalar characters

The field is `F : Type uF`, with `Field F`, `ValuativeRel F`, its given
`TopologicalSpace F`, and `IsNonarchimedeanLocalField F`. The universe `uF` is
arbitrary. There is no characteristic-zero assumption or specialization to a
p-adic field. Let `v = ValuativeRel.valuation F` and `O = v.integer`.
The user supplies `ϖ : Fˣ` and
`hϖ : Iwasawa.IsUniformizingElement v ϖ`. This witness says that
`0 < v(ϖ) < 1` (positivity also follows because `ϖ` is a unit of the field)
and that each nonzero field element has valuation an integer power of `v(ϖ)`.

`ord hϖ a` chooses that integer for `a : Fˣ`.
`valuation_eq_pow_ord` records its defining equality, and
`ord_eq_of_valuation` proves uniqueness using strict antitonicity of integer
powers of `v(ϖ)`. The lemmas `ord_one`, `ord_mul`, `ord_zpow`,
`ord_uniformizer`, and `ord_eq_zero_iff` give the usual order laws.

For an arbitrary `z : ℂˣ`, `character hϖ z : Fˣ →* ℂˣ` is

\[
\chi_z(a)=z^{\operatorname{ord}(a)}.
\]

Here `ℂˣ` denotes all nonzero complex numbers, with no modulus-one restriction.
`character_uniformizer`, `character_unit`, and
`character_uniformizer_pow_mul` prove respectively its value `z` at `ϖ`, its
triviality when `v(a)=1`, and the formula `χ_z(ϖ^m * a)=z^m` for such `a`.
The kernel is open: the order kernel is the preimage of the open valuation
sphere `v(a)=1`, and is contained in the character kernel.
`smoothCharacter` bundles this proved open-kernel property with the actual
homomorphism.

## The Borel and normalization

For `n : ℕ`, put `r=n+1`. `Borel n` abbreviates the actual
`upperTriangularSubgroup r F` of `Langlands.GeneralLinear r F`.
`borel_eq_singleton_parabolic` identifies it with the existing singleton-block
parabolic. `diagonalUnit n i` is the diagonal-entry homomorphism to `Fˣ`;
its entries are nonzero because their product is the nonzero determinant.
`inducingCharacter hϖ n z` is the product of the scalar characters along these
homomorphisms, for `z : Fin r → ℂˣ`.

The supplied `q : ℕ` must satisfy `IsResidueCardinality (F := F) q`, defined as

\[
q=\operatorname{Nat.card}(\operatorname{ResidueField}(O)).
\]

Thus the residue size is tied to the given valuation ring.
`residueCardinality_pos` proves positivity, and `sqrtResidueUnit` is the complex
unit obtained from the positive real square root of `q`. With zero-based
indices `i : Fin r`, `halfModulusCharacter` is explicitly

\[
\delta_B^{1/2}(b)
 = (\sqrt q)^{-\sum_i (n-2i)\operatorname{ord}(b_{ii})}.
\]

`modulusExponent` proves additivity of the exponent under Borel multiplication;
`halfModulusCharacter_apply` exposes the displayed complex value.
This is the positive-square-root normalization corresponding to the source's
`|a|=q^{-ord(a)}` convention, since the upper-Borel exponent of `|b_ii|` is
`(r-1)/2-i`. No separately supplied absolute value or square-root branch is
used. `halfModulusCharacter_torus` proves agreement with the existing
`Langlands.GeneralLinear.Spherical.halfModulus q lam` on actual diagonal
uniformizer powers. No comparison with a separate Haar-modulus definition is
asserted here.

`normalizedCharacter` multiplies this half modulus by `inducingCharacter`.
It is trivial on `Borel n ∩ integralSubgroup O n`, because every diagonal entry
there has valuation one, by `Iwasawa.valuation_diag_eq_one`.
`integralOpenSubgroup` bundles the actual integral matrix subgroup with its
openness for the given topology. Its intersection with the Borel proves
`isOpen_ker_normalizedCharacter`; `normalizedSmoothCharacter` is the resulting
bundled smooth character.

## Induced representation and spherical section

`PrincipalSeries hϖ n hq z` is the existing `Induction.SmoothFunctions` space
for the scalar `characterRepresentation` of `normalizedCharacter`.
Its elements are actual complex-valued functions on `GL_r(F)` satisfying
Borel covariance and invariant on the right by some open subgroup.
`principalSeries hϖ n hq z` is `Induction.smoothInduced`, acting by right
translation. There is no compact-support condition.

The accessor `value hϖ n f g` evaluates an induced function at the actual
matrix `g`. `covariance` and `rightTranslation` give exactly

\[
f(bg)=\delta_B^{1/2}(b)\Bigl(\prod_i\chi_{z_i}(b_{ii})\Bigr)f(g),
\qquad (\rho(g)f)(x)=f(xg).
\]

`principalSeries_smooth` proves `IsSmooth` for this representation using the
existing theorem about the smooth induced carrier.

To construct the spherical section, `exists_borel_integral` bundles the
existing `Iwasawa.exists_upperTriangular_mul` decomposition as `g=bk`, with
`b` in the actual Borel and `k` in the actual integral subgroup. `borelFactor`
chooses its Borel factor. `normalizedCharacter_factors_eq` proves that the
character value is independent of this choice: from `bk=cl`, the element
`c⁻¹b=lk⁻¹` lies in the integral subgroup and the character is trivial there.
`sphericalValue g` is this well-defined character value. Its proved covariance
and integral right invariance allow `smoothFunctionOf` to construct
`sphericalSection hϖ n hq z` in the actual induced carrier. Neither a section
nor a fixed-line property is an input.

The principal evaluation and invariance accessors are:

| Declaration | Conclusion |
| --- | --- |
| `sphericalSection_value` | Evaluation is the constructed `sphericalValue`. |
| `sphericalSection_borel_mul_integral` | Its value at `bk` is the normalized Borel character of `b`. |
| `sphericalSection_covariance` | The explicit half-modulus and product-character covariance above. |
| `sphericalSection_one`, `sphericalSection_integral` | Its value is one at the identity and throughout the integral subgroup. |
| `sphericalSection_mul_integral` | Pointwise right invariance under that subgroup. |
| `sphericalSection_fixed` | The corresponding equality in the induced representation. |
| `sphericalSection_ne_zero` | Nonvanishing, by evaluation at the identity. |
| `sphericalSection_torus` | At `Iwasawa.torus ϖ lam`, its value is `Spherical.halfModulus q lam * ∏ i, (z i : ℂ) ^ lam i`. |

The module adds only this construction and its supporting laws. It leaves the
existing essential-vector and conductor definitions and their imports
unchanged. Irreducibility, ordered spherical cyclicity, Whittaker maps and
injectivity, Casselman–Shalika comparison, Hecke eigenvalue identities, and
local-factor identities are separate subsequent obligations.
