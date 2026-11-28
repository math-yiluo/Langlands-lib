# The Siegel bound for weak constant terms on the Levi, by reduction

Module `Langlands.Global.AdelicWeakConstantTermLeviSiegelBound`. Its main theorem,
`weakConstantTermLeviSiegelBound_of_reduction`, proves
`WeakConstantTermLeviSiegelBoundStatement` (module
`Langlands.Global.AdelicWeakConstantTermLeviTemperedReduction`; Delorme 2023, Lemma 3.8 (ii))
from two statements taken as hypotheses:

- `LogSquareIntegrableSiegelDerivativeBoundsStatement` (module
  `Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeBounds`), the logarithmic Siegel
  bounds for log-square-integrable automorphic forms and their derivatives;
- `SiegelSetupConjugacyStatement` (module `Langlands.Global.AdelicSiegelSetupConjugacyStatement`),
  the rational conjugacy of the Siegel sets of two algebraic Siegel setups.

This module does not prove these two statements. All declarations of the module are proved.

| Declaration | Kind | Content |
| --- | --- | --- |
| `map_map_apply` | theorem | adelic points of a composite morphism |
| `exists_adelicLogHeight_mul_left_le` | theorem | `σ(q x) ≤ L σ(x)` for a fixed `q` |
| `StandardParabolicFamily.isClosedSubgroup_levi` | theorem | `M_J → P_J → G` is a closed subgroup |
| `StandardParabolicFamily.isRepresentedBy_standardLevi` | theorem | it represents `standardLevi fam.i fam.ν J` |
| `StandardParabolicFamily.isMaximalSplitTorus_torus` | theorem | `fam.torus J` is a maximal split torus of `M_J` |
| `StandardParabolicFamily.isGenericCocharacter_torus` | theorem | `fam.ν` is generic for `fam.torus J` |
| `StandardParabolicFamily.subset_simpleRelativeRoots_torus` | theorem | `J` consists of simple roots of `M_J` |
| `StandardParabolicFamily.exists_leviSiegelAlgebraicSetup` | theorem | `M_J` has a Siegel setup on `(fam.T, fam.torus J, fam.ν)` |
| `StandardParabolicFamily.exists_leviSiegelBound_of_chamberGrowth` | theorem | the Levi bound for that setup, from the chamber bound on `G` |
| `weakConstantTermLeviSiegelBound_of_reduction` | theorem | the reduction |

Here `σ(x) = adelicLogHeight F G rho x = 1 + log max(1, ‖x‖_ρ)`.

## The Levi of a standard parabolic

For a standard parabolic family `fam` and a standard index `J`, `fam.torus J ≫ fam.l J ≫ fam.p J
= fam.i`. The Levi embedding is closed (`IsRationalLeviSubgroup` and `IsParabolicSubgroup` of
the compatibility data) and represents the standard Levi (`levi_eq`). Hence `fam.torus J` is a
maximal split torus of `M_J` (`IsMaximalSplitTorus.of_comp`), the relative roots of `M_J` are
relative roots of `G` (`relativeRoots_subset_of_factor`), so `fam.ν` stays generic. A simple
root `β ∈ J` of `G` is a root of `M_J`: the compatibility data give a standard cocharacter `ζ`
with `range (l ≫ p) = Dynamic.centralizer ζ` and `⟨β, ζ⟩ = 0`, and
`mem_relativeRoots_of_pairing_eq_zero` applies. It is positive, and not a sum of two positive
roots of `M_J`, since these are positive roots of `G`. With `M_J` connected reductive,
`exists_isSiegelAlgebraicSetup` gives the Siegel setup of `M_J`.

## The bound for the Siegel setup of the family

`exists_leviSiegelBound_of_chamberGrowth`: assume `StandardNestedHalfModulusCompatibilityStatement`,
an algebraic Siegel setup `(fam.T, fam.i, fam.ν, T₀, j)` of `G`, a closed matrix embedding `rho`
of size `N > 0`, and `ψ = ∑_{λ ∈ s} c_λ` with unitary normalized exponents along `P_J` and the
logarithmic Siegel chamber bound of `G` for that setup, as in
`exists_leviChamber_bound_of_unitaryExponents`. Let `(fam.T, fam.torus J, fam.ν, T₁, k)` be an
algebraic Siegel setup of `M = M_J`, `C` compact factors, `t` a threshold, `Ω ⊆ M(𝔸)` and
`Ω' ⊆ G(𝔸)` compact. Then there are `e` and `B` with

`‖ψ(ι(m) w)‖ ≤ B δ_M(a)^{1/2} σ_M(m)^e`

for every `m ∈ M(𝔸)¹` with `IsSiegelPoint F M fam.T (fam.torus J) fam.ν T₁ k C t Ω a m` and every
`w ∈ Ω'`, where `ι = map F M G (fam.l J ≫ fam.p J)`, `δ_M` is the Siegel modulus of the setup of
`M` and `σ_M` the logarithmic height of `M` for `rho.restrict (fam.l J ≫ fam.p J)`.

Proof. By `exists_isCompact_siegelPoint_eq_mul`, `m = a_M(a) y` with `y` in a compact `Y`. The
image of `a` in `fam.T(𝔸)` is positive and its image in `G(𝔸)` is `ι(a_M(a)) ∈ G(𝔸)¹`
(`IsSiegelAlgebraicSetup.positiveMap_mem_normOne`, `map_normOneSubgroup_le`), so
`exists_siegelTorus_lift_of_characterLog_eq_zero` gives `b` in the Siegel torus of `G` with
`a_G(b) = ι(a_M(a))`. For `β ∈ J`, `log|β(b)| = log|β(a)| ≥ log t`, since `β` is a simple root of
`M`. `exists_leviChamber_bound_of_unitaryExponents` with the compact set `ι(Y) Ω'` bounds
`ψ(a_G(b) ι(y) w) = ψ(ι(m) w)` by `B δ_G(b)^{1/2} (1 + log H(a_G(b)))^e`. The moduli agree,
`δ_G(b) = δ_M(a)` (`siegelModulus_eq_levi_of_normOne`). Finally
`H(a_G(b)) = H_M(m y⁻¹)` (`adelicHeight_map_eq_adelicHeight_comp`), and
`log H_M(x) ≤ log N^{[F:ℚ]} + σ_M(x)` (`log_adelicHeight_le`) with
`σ_M(m y⁻¹) ≤ L σ_M(m)` (`exists_adelicLogHeight_mul_le`), so
`1 + log H(a_G(b)) ≤ (1 + log N^{[F:ℚ]} + L) σ_M(m)`.

## The reduction

`weakConstantTermLeviSiegelBound_of_reduction`: the two statements above imply
`WeakConstantTermLeviSiegelBoundStatement`.

Proof. Fix the data of the statement.

- If `N = 0`, the closed embedding into `GL_0` makes `G(𝔸)` trivial. The image of the torus
  coordinate in `T(𝔸)` is then `1`, since `T(𝔸) → M(𝔸) → G(𝔸)` is injective, so every root has
  absolute value one at `a` and `siegelModulus = 1`; the bound holds with `e = 0` and
  `B = ‖ψ(1)‖`.
- If `N > 0`: `exists_isSiegelAlgebraicSetup` gives a Siegel setup of `G` on `fam.T`. The first
  hypothesis gives the logarithmic Siegel chamber bound of the constant term of `Φ`
  (`adelicSiegelConstantTermGrowth`), and the weak constant term `ψ` lies in the split-component
  orbit span of that constant term (`IsWeakConstantTerm.mem_splitComponentOrbitSpan`), so it has
  the chamber bound as well (`hasSiegelChamberGrowth_of_mem_splitComponentOrbitSpan`). By
  definition `ψ` is the sum of the components with `Re λ = 0` of an exponent decomposition. Each
  component is left invariant under `ι(M(F))`, a subgroup of the parabolic quotient subgroup.
  The second hypothesis, applied to `M` with the given setup and the setup of the family, gives
  `q ∈ M(F)` carrying the Siegel set of `(C, t, Ω)` into a Siegel set of the setup of the family,
  with equal moduli. Then `ψ(ι(m) w) = ψ(ι(q m) w)`, `exists_leviSiegelBound_of_chamberGrowth`
  bounds it by `B δ_M(a)^{1/2} σ_M(q m)^e`, and `σ_M(q m) ≤ L σ_M(m)`
  (`exists_adelicLogHeight_mul_left_le`).

## Sources

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering): Proposition 3.6 and
Definition 3.7, p. 13, (3.5)–(3.6) and Lemma 3.8 (ii), p. 14. Delorme derives the bound on the
Levi from the temperedness of the form and Proposition 3.6 for the Levi with a compact subgroup
in good position. The proof here is derived and takes a different route: the chamber bound on
`G`, the unitarity of the exponents of the weak constant term along the split component of
`P_J` (Definition 3.7), extrapolation along a ray of that split component
(module `Langlands.Global.AdelicWeakConstantTermChamberExtrapolation`), and the conjugacy of
Siegel setups for the passage to an arbitrary Siegel setup of the Levi. The compact subgroup
`K` enters only through the hypotheses of `adelicSiegelConstantTermGrowth` and the automorphy
of the components of `ψ`.
