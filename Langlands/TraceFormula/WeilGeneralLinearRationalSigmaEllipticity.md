# Rational σ-ellipticity from a finite place of the base

`Langlands.TraceFormula.weilGeneralLinearRationalSigmaEllipticity.{u}` proves
`WeilGeneralLinearRationalSigmaEllipticityStatement.{u}`. For a cyclic extension
of number fields `L/K`, it takes a principal adelic point of `Res_{L/K} GL_n`
that is σ_v-elliptic at a finite place `v` of `K` and gives its rational
matrix `δ ∈ GL_n(L)` together with σ-ellipticity over `K`.
[Statement](WeilGeneralLinearRationalSigmaEllipticityStatement.md)

## Rational coordinates

The rational subgroup is the image of the principal point map, so write the
given point as the image of `q ∈ (Res_{L/K} GL_n)(K)`. The proof chooses
`δ = rationalWeilGLEquiv K L n q`. The map `Φ` in the statement is
`cyclicWeilAdelicMap`. To compute it on `q`, the proof uses
`AdelicWeilRestriction.adelicPointsEquiv_rational`, then
`AdelicGroupPoints.rational_naturality` for the `GL_n` base-change isomorphism
and `GeneralLinearGroupPoints.adelicHomeomorph_rational`. These give the
diagonal image of the matrix read from the upper rational point.
[Adelic map](CyclicAdelicTests.md) ·
[Weil comparison](../Global/AdelicWeilNormOneComparison.md) ·
[Rational point maps](../Global/AdelicGroupPoints.md) ·
[Matrix homeomorphism](../Global/AdelicGroupPointTopology.md)

The helper `baseChange_affineEntry` computes an entry after the base-change
isomorphism. It uses `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom`,
`GeneralLinear.pointsEquiv_apply_apply` and `baseChangePointsEquiv_left` to
read the entry on the projected point. The translations between global
sections and affine coefficients are
`Corepresented.map_affineSectionsIso_pointsEquiv` and
`Corepresented.affineSectionsIso_hom_ringHom`. Then `baseChange_rationalMatrix`
uses `affinePointsBaseChangeMulEquiv_symm_left` and
`GeneralLinear.affinePointsEquiv_entry_evaluation` to compare the two
matrices entry by entry.
[GL base change](../GroupScheme/Dynamic/GeneralLinearBaseChange.md) ·
[GL point coordinates](../GroupScheme/GeneralLinear.md) ·
[Pullback projection](../AbelianScheme/KernelBaseChange.md) ·
[Affine section comparison](../GroupScheme/CorepresentedAffineComparison.md) ·
[Base-change point equivalence](../GroupScheme/AffinePointBaseChangeSmooth.md) ·
[Entry evaluation](../GroupScheme/GeneralLinearPointTopology.md)

The upper rational points use `AffineWeil.basePointsEquiv`, which applies the
tensor-unit map `L ⊗[K] K → L` to the tensor-valued point. By
`affinePointsBaseChangeMulEquiv_naturality`, this map commutes with forgetting
the base change via `AffineWeil.unitGroundPointsEquiv`.
`GeneralLinear.affinePointsEquiv_naturality` computes the resulting matrix
by applying the tensor-unit map to each entry, which is the definition of
`rationalWeilGLEquiv`. Thus `Φ` takes the principal image of `q` to
`AdelicGL.rational L n δ`. By `localPointsEquiv_atPlace_rational`, the
component at `v` is the image of the same `δ` under the coefficient map
`L → K_v ⊗[K] L`, `b ↦ 1 ⊗ b`.
[Rational Weil comparison](../GroupScheme/AffineWeilRestrictionTopology.md) ·
[Naturality under base change](../GroupScheme/AffineWeilUnit.md) ·
[Ground-point comparison](../GroupScheme/AffineWeilUnitGalois.md) ·
[GL affine naturality](../GroupScheme/GeneralLinear.md) ·
[Local rational coordinates](RationalLocalGeneralLinear.md)

## Descent of ellipticity

Part (1a) of `cyclicNormLemma` gives `γ ∈ GL_n(K)` associated with `δ`.
By `localize_normAssociated`, the image `γ_v` over `K_v` is associated
with the localized `δ`. Local σ_v-ellipticity supplies a second associate
`γ' ∈ GL_n(K_v)` with separable irreducible characteristic polynomial.
`isCyclicAlgebra_localGalois` makes the local tensor algebra cyclic, so
part (1b) of `cyclicNormLemma` over `K_v` gives conjugacy of `γ_v` and `γ'`.
[Cyclic norm lemma](../BaseChange/CyclicNormLemma.md) ·
[Norm localization](RationalLocalGeneralLinear.md) ·
[Local cyclic algebra](GeneralLinearBaseChangeLocal.md)

Mathlib's `Matrix.charpoly_units_conj'` and `Matrix.charpoly_map` identify the
characteristic polynomial of `γ'` with the image of the characteristic
polynomial of `γ` under `K → K_v`. `Polynomial.separable_map` descends
separability and `Polynomial.Monic.irreducible_of_irreducible_map`, applied
with `Matrix.charpoly_monic`, descends irreducibility. The matrix `γ` and its
association with `δ` then witness `IsSigmaElliptic σ l δ`.
[Elliptic characteristic polynomials](../JacquetLanglands/RegularElliptic.md) ·
[Norm association and σ-ellipticity](../BaseChange/Norm.md)

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mémoires de la SMF 124 (2011), registered source
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
I.2.1–I.2.2, Lemme (1) and the following definition (printed pp. 10–12),
give the cyclic algebra, norm and associate used here. I.2.3 (pp. 13–14)
and II.2.2 (p. 63) give the ellipticity conventions. II.6.1 (p. 118)
identifies the algebra at a place of the base, and II.6.4 (pp. 120–121)
uses local σ-elliptic support and rational classes with elliptic norm over
the base field. The Lean proof derives this local-to-rational implication
for number fields.
