# The global upper bound for the actual spherical function

Worker 248, Task 5460. Module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiGlobalUpperBoundStatement`
states `RationalXiGlobalUpperBoundStatement.{u}` at arbitrary universe `u`. The
global estimate itself is a proof target. The module proves its reformulation
in the `XiUpperBound` interface and its implication for `UnipotentXiBound`.

Let `F` be a nonarchimedean local field, `G` a connected reductive affine group
of finite type over `F`, `i : S → G` a maximal split torus, and `ν` generic.
Assume one compact open `K0` has `SimultaneousStandardBasisAt i ν K0` and
`FiniteCartanCovering F i ν K0`. For any compact open `K` with
`G(F) = P₀(F) K` and any closed matrix representation `ρ` of nonzero size, the
statement asks for a natural number `D` and positive real `C` such that, for all
`g ∈ G(F)`,

```
Ξ_K(g) ≤ C φ_K(g) (1 + σ_ρ(g))^D,
φ_K(p k) = δ₀(p)^(1/2).
```

Here `Ξ_K = rationalXi`, `φ_K = iwasawaWeight hPK
(rationalMinimalModulus i ν)` and `σ_ρ = rationalHeight ρ`. The structural
compact subgroup, the subgroup defining `Ξ`, and the subgroup preserving the
height may differ. No analytic bound is assumed by this proposition.

This is a derived global form of the estimate in the proof of Waldspurger's
Lemma II.4.4 (printed p.262). The source applies the upper bound of II.1.1 to a
Cartan representative and uses II.3.2 to compare its modulus with the Iwasawa
modulus of the original point. It writes this for `g = m ū`; the same argument
depends only on the point's Cartan decomposition and gives the displayed global
estimate. Our statement retains the supplied structural basis and Cartan
covering used to formalize those inputs and allows the arbitrary compact
Iwasawa subgroup and matrix representation used by the actual-point Library.

The proved helper `RationalXiGlobalUpperBoundStatement.xiUpperBound` simply
converts the natural exponent into a real exponent in `XiUpperBound`.
`RationalXiGlobalUpperBoundStatement.unipotentXiBound` then applies the
published Iwasawa covariance formula:

```
φ_K(m u) = φ_K(m) φ_K(u),   m ∈ Z_G(S)(F).
```

Every such `m` belongs to `P₀(F)`. The conclusion holds for any subgroup `U`,
and in particular for the opposite radical of any standard parabolic. This
helper is conditional on the named global proposition; it does not prove that
proposition or establish weighted integrability. Using the standard radical
with the same minimal parabolic would give `φ_K(u) = 1`, so it would not by
itself supply the integrable weight needed in II.4.5.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), literature ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Relevant passages: II.1, printed pp.250–251 (spherical function and II.1.1);
II.3.2, printed p.255 (Cartan modulus comparison); II.4.4 and its proof,
printed p.262 (the combined bound). The global formulation and arbitrary
compact-subgroup adaptation are derived here, not separately numbered source
claims.
