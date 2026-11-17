# Weighted integrability on an actual opposite unipotent radical

Worker 248, Task 5460. Module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalUnipotentWeightIntegrabilityStatement`
states `RationalUnipotentWeightIntegrabilityStatement.{u}` at arbitrary universe
`u`. This estimate is a proof target. Its included helper converts the
natural-exponent conclusion into `UnipotentWeightIntegrable`.

Let `F` be a nonarchimedean local field and `G` a connected reductive affine
group of finite type over `F`. Let `i : S → G` be a maximal split torus, `ν`
generic and `ζ` a standard cocharacter for a subset `J` of the simple relative
roots. The subgroup being integrated is the actual opposite radical

```
Ū_J(F) = U(-ζ)(F) = oppositeUnipotent i ζ,
```

defined by the dynamic contraction subgroup of the inverse cocharacter
`G_m → S → G`. This is the opposite of the standard radical `U_J(F)`;
`opposite_isSemidirectDecomposition` gives its parabolic the same actual
standard Levi. It is not `U_J(F)` in the chamber defining the weight.

Assume a compact open `K0` has `SimultaneousStandardBasisAt i ν K0` and
`FiniteCartanCovering F i ν K0`. For any compact open Iwasawa factor `K`,
any closed matrix representation `ρ` of nonzero size, and any Haar measure
`ν_U` on `Ū_J(F)`, the proposition asks for `d ∈ ℕ` with

```
∫⁻_{Ū_J(F)} φ_K(u) (1 + σ_ρ(u))^(-d) dν_U(u) < ∞,
φ_K(p k) = δ₀(p)^(1/2).
```

The Lean integrand uses `ENNReal.ofReal` of this nonnegative real function.
The weight is `iwasawaWeight hPK (rationalMinimalModulus i ν)`; with the usual
minimal Iwasawa components it is exactly `δ₀(m₀(u))^(1/2)`.
The height is `rationalHeight ρ`, the logarithm of the matrix norm. The
statement assumes no weighted integrability or spherical estimate.

This is Waldspurger's Lemma II.4.2, printed p.261, realized on actual rational
points. The source fixes a special maximal compact subgroup and proves the
estimate by the level-set estimate II.4.1 and the height/modulus comparisons
of II.3. The Library formulation retains supplied structural basis and Cartan
data, and allows `K` and `ρ` to vary; that compact-subgroup and height
adaptation is derived content. It makes no assertion that the displayed
integral converges over the standard radical with the same minimal weight.
Transport to the opposite-parabolic convention of
`RationalConstantTermEstimateStatement` remains a consumer obligation.

The only proved helper here is
`RationalUnipotentWeightIntegrabilityStatement.unipotentWeightIntegrable`.
It applies the named proposition to the supplied data, and regards its natural
number `d` as a real number in `UnipotentWeightIntegrable`. It does not prove
II.4.2. Polynomial volume estimates for matrix-norm balls alone do not prove
this assertion about logarithmic height.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), literature ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Relevant passages: II.4 opening and II.4.1, printed pp.259–261 (opposite
radical and its level sets); Lemma II.4.2 and its proof, printed p.261;
Proposition II.4.5 and its proof, printed pp.262–263.
