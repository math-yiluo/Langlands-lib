# The regular-patch Eisenstein comparison for finite families, for fixed group data

Module `Langlands.Global.AdelicEisensteinFamilyRegularComparison` defines the predicate
`FamilyRegularComparison` and proves `FamilyRegularComparison.single`.

## The predicate

`FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hK hK' rho hsmooth hcalc`
is a proposition about fixed data:

- a group scheme `G` over a number field `F`, affine and locally of finite type;
- closed immersions `p : P → G` and `q : Q → G`, morphisms `l : M → P`, `l' : M' → Q`,
  `a : A → M`, `a' : A' → M'`, and root presentations `r` of `(p, l, a)` and `r'` of
  `(q, l', a')` (`ParabolicRootPresentation`), with split-torus witnesses `hA`, `hT`, `hA'`,
  `hT'`. The compatibility field of a root presentation makes `p` and `q` parabolic subgroups
  and `l`, `l'` rational Levi subgroups;
- morphisms `iU : U → P` and `iV : V → Q`, with `iV ≫ q` a closed immersion;
- a morphism `π' : Q → M'`, a rational point `w` of `G` and a morphism `c : M' → M`;
- a subgroup `K` of `G(𝔸)` with Iwasawa coverage `hK` for `p` and `hK'` for `q`
  (`IsIwasawaCompact`);
- a matrix representation `rho : MatrixRepresentation G (Fin N)`, a morphism of group schemes
  to `GL_N`, with smooth-structure data `hsmooth`, `hcalc`.

The predicate imposes no further conditions on these data. In particular, it does not ask
that `iU` and `iV` be geometric unipotent radicals, that `l' ≫ π' = 𝟙`, that `(w, c)` be a
Weyl conjugation, or that `rho` be a closed embedding. These are hypotheses of
`FamilyRegularComparison.of_standardFamily` (module
`Langlands.Global.AdelicEisensteinRegularComparisonPassage`), which proves the predicate.

The predicate says: for every finite index type `Ix` in universe `v`, every family
`φ : Ix → (G(𝔸) → ℂ)` of functions satisfying `IsAutomorphicFunctionOn` for the subgroup
`parabolicQuotientSubgroup F p iU l` (the join `U(𝔸) M(F)` of the images of `U(𝔸)` under
`iU ≫ p` and of `M(F)` under `l ≫ p`), the compact
`K_∞ = K.comap (ofInfinite F G)` and `rho`, every family `b : Ix → (X^*(P) ⊗ ℂ → ℂ)` of
coefficients meromorphic with domain `Db` (`IsMeromorphicInCoordinatesOn`), every
`EP : X^*(P) ⊗ ℂ → G(𝔸) → ℂ` meromorphic in `λ` with domain `DP` at every `g` and equal to
`∑ v, b v λ · E(φ v, λ)` for `λ` sufficiently regular for `r`, and every finite index type `Jx`
in universe `w` with functions `ψ i` satisfying `IsAutomorphicFunctionOn` for
`parabolicQuotientSubgroup F q iV l'`, `K_∞` and `rho`, and coefficients `coeff i` meromorphic
with domain `D` such that

`∑ v, b v λ · M(w, λ)(φ v) = ∑ i, coeff i λ · ψ i`

for `λ` sufficiently regular for `r` (`IsIwasawaCompact.intertwiningOperator`), the following
holds for every real `R`: there are linear coordinates `e : ℂᵐ ≃ X^*(P) ⊗ ℂ` and a nonempty
open set `O ⊆ ℂᵐ` such that at every `x ∈ O` the transported parameter
`wλ = weylParameter l c π' (e x)` is `R`-regular for `r'` and

`EP (e x) g = ∑ i, coeff i (e x) · E_Q(ψ i, wλ)(g)` for all `g`.

The Eisenstein series are `IsIwasawaCompact.eisensteinSeries` for `hK` and `hK'`, and
regularity is `ParabolicRootPresentation.IsRegularParameter`. The universes `v` and `w` of the
index types are parameters of the predicate, so that the transport theorems of the other
modules may enlarge the index types.

The predicate is the conclusion of
`EisensteinFunctionalEquationRegularComparisonStatement` (module
`Langlands.Global.AdelicEisensteinFunctionalEquationRegularComparisonStatement`) for finite
families of inducing forms, with the group data fixed.

## The case of one inducing form

`FamilyRegularComparison.single` derives the one-form conclusion from
`FamilyRegularComparison.{u, 0, 0}`: given `φ`, `EP` with `EP λ = E(φ, λ)` for regular `λ`, and
`M(w, λ)φ = ∑ i, coeff i λ · ψ i` for regular `λ` (`ψ` indexed by `Fin k`), the conclusion of
the predicate holds. The proof applies the predicate to the family indexed by `Fin 1` with
`φ 0 = φ` and the constant coefficient `1`, meromorphic on the whole space (built directly as a
constant holomorphic function in every coordinate system), and simplifies the sums over
`Fin 1`.

## Source

The identity is Bernstein–Lapid Theorem 2.3(4) on a regular patch: J. Bernstein and E. Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2,
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`. The finite families
with meromorphic coefficients are not in the source. They make the predicate stable under a
change of the Iwasawa compact, where one inducing form for one compact becomes a finite sum of
inducing forms with exponential coefficients for the other.
