# Constant terms preserve integrals over a rational quotient

Module `Langlands.Global.AdelicConstantTermAverage`, namespace
`Langlands.Global.ConstantTermAverage`.

## Definitions

- `lowerConstantTerm F G U f g` is the nonnegative constant term along a subgroup functor `U`
  of `G`:
  `∫_{U(F) \ U(𝔸)} f(u g) du`. The integral uses the Library's mass-one measure
  `normalizedRationalQuotientHaarMeasure F G U` and the representatives `Quotient.out`. For
  `U = SubgroupFunctor.range j` this is the same integral as the Library's complex
  `subgroupConstantTerm F j`, with `[0, ∞]`-valued integrands.
- `rationalFundamentalDomain F G U` is the Library's Borel fundamental domain
  `LeftCosetSpace.fundamentalDomain` of `U(F)` in `U(𝔸)`.
- `conjEquiv F G U Λ hnorm l` is conjugation `w ↦ l w l⁻¹` by `l ∈ Λ`, as a topological group
  automorphism of `U(𝔸)`, when `Λ` normalizes `U(𝔸)` (`hnorm`).

## Main statement

`AdelicConstantTermIntegralStatement`, proved by `adelicConstantTermIntegral`. Its data are
the following.

- `F` is a number field, `G` an affine group scheme over `F` locally of finite type, and `U` a
  subgroup functor of `G` whose adelic points are closed in `G(𝔸)` and whose quotient
  `U(F) \ U(𝔸)` is compact.
- `Λ ≤ G(𝔸)` is discrete and contains the principal image `rationalSubgroup F G U` of `U(F)`.
- Conjugation by every `l ∈ Λ` maps `U(F)` into `U(F)` and `U(𝔸)` into `U(𝔸)`.

`U(𝔸) ∩ Λ` may be larger than `U(F)`; this is not needed.

Then every measurable left `Λ`-invariant `f : G(𝔸) → [0, ∞]` satisfies two conclusions:

1. `lowerConstantTerm f (l g) = lowerConstantTerm f g` for `l ∈ Λ`, so the constant term
   descends to `Λ \ G(𝔸)`;
2. `∫_D lowerConstantTerm f dg = ∫_D f dg` over the Library's Borel fundamental domain
   `D = LeftCosetSpace.fundamentalDomain Λ`, for the Haar measure of `G(𝔸)`. By the definition
   of the Library's quotient measures, this says that the constant term preserves integrals over
   `Λ \ G(𝔸)`.

The intended case is `Λ = P₀(F)` and `U = U_P` for a standard parabolic `P`. The identity
`∫_{P₀(F)\G(𝔸)} CT_P f = ∫_{P₀(F)\G(𝔸)} f` is the measure statement behind the Harish-Chandra
decomposition in Bernstein–Lapid, J. Amer. Math. Soc. 37 (2024), §7.3, p.214. There `CT_P` is
the orthogonal projection of a weighted `L²` space onto the functions that factor through
`P₀(F) U_P(𝔸) \ G(𝔸)`. The structural hypotheses (containment and normality) are explicit
premises of the statement. For `U_P` normal in `P ⊇ P₀` they follow from the Library's
`AdelicGroupPoints.rationalImage_comp_le`, `conj_mem_rationalImage` and
`conj_mem_adelicPoints_range` (module `Langlands.Global.EisensteinConstantTerm.Points`).

## Proof

- `isInvInvariant_of_isMulRightInvariant`: a right-invariant Haar measure on a second-countable
  locally compact group is inversion invariant. The inverse measure is left invariant, hence
  `c` times the measure. Applying inversion twice gives `c² = 1`, so `c = 1`.
- `measurePreserving_of_preserves_fundamentalDomain`: a topological automorphism `φ` that
  preserves a discrete subgroup `Γ` with a fundamental domain `C` of finite positive measure
  preserves Haar measure. Again `φ_* μ = c μ`; the preimage `φ⁻¹ C` is another fundamental
  domain of `Γ`, so it has the same measure as `C`, and `c = 1`.
- Haar measure on `U(𝔸)` is right invariant by the Library's
  `haar_isMulRightInvariant_of_compactRationalQuotient` (compact quotient). So it is
  inversion invariant, and each `conjEquiv l` preserves it (`measurePreserving_conjEquiv`),
  because conjugation by `l` and by `l⁻¹` maps `U(F)` into itself
  (`mem_rationalSubgroup_conjEquiv_iff`).
- `lowerConstantTerm_eq`: for `f` left invariant under `U(F)`, the constant term equals
  `ν(C)⁻¹ ∫_C f(v g) dν(v)`, where `ν` is Haar measure on `U(𝔸)` and `C` the fundamental domain.
  It follows from the definitions of the quotient measures and the Library's
  `EisensteinConstantTerm.lintegral_out_eq`.
- `setLIntegral_lowerConstantTerm` applies `FibreAverage.setLIntegral_fibreAverage` (module
  `Langlands.Analysis.FundamentalDomainFibreAverage`) with `H = G(𝔸)`, `j` the inclusion of
  `U(𝔸)`, `Γ = U(F)` and the conjugations above. It then cancels `ν(C)`, which is finite and
  nonzero because `U(F) \ U(𝔸)` is compact and its quotient measure is nonzero.
- `lowerConstantTerm_mul_left`: for `l ∈ Λ`, `f(v l g) = f((l⁻¹ v l) g)`. The substitution
  `v ↦ l⁻¹ v l` preserves `ν` and carries `C` to another fundamental domain of `U(F)`. The integral
  of a `U(F)`-invariant function is the same over both fundamental domains
  (`setLIntegral_comp_symm_eq`).

## Scope

The module does not instantiate the structural hypotheses for standard parabolics, and it does
not construct the constant term as an operator on weighted `L²` spaces. Those are separate steps on the route to Bernstein–Lapid
Theorem 7.2.
