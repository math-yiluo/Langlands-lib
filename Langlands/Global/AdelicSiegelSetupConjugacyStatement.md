# Rational conjugacy of Siegel sets of two algebraic Siegel setups

Module `Langlands.Global.AdelicSiegelSetupConjugacyStatement` states
`Langlands.Global.SiegelSetupConjugacyStatement`. It does not prove it.

| Declaration | Kind | Source |
| --- | --- | --- |
| `SiegelSetupConjugacyStatement` | statement | derived: Borel–Tits 1965, Théorème 4.13 b), Proposition 4.7, Corollaire 4.16, Théorème 4.21, applied to the Siegel sets of Mœglin–Waldspurger I.2.1 and Delorme 2023, (2.3) |

## Statement

Let `F : Type` be a number field and `G` an affine group scheme over `F`, locally of finite type
and connected reductive (`IsConnectedReductive G`). The Siegel data are those of the module
`Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`, with the meaning given in its
Markdown page. Let

- `(T, i, ν, T₀, j)` and `(T', i', ν', T₀', j')` be two algebraic Siegel setups of `G`
  (`IsSiegelAlgebraicSetup F G T i ν T₀ j` and `IsSiegelAlgebraicSetup F G T' i' ν' T₀' j'`);
- `C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)` be
  compact factors of the first setup, whose compact subgroup is an arbitrary compact subgroup of
  `G(𝔸)`;
- `t : ℝ≥0ˣ` be a threshold and `Ω ⊆ G(𝔸)` a compact set.

Then there are

- a rational point `q ∈ G(F)` (`q ∈ rationalSubgroup F G`),
- compact factors
  `C' : CompactFactors F G (Standard.unipotentScheme i' ν' ∅) (Standard.leviScheme i' ν' ∅)`
  of the second setup,
- a threshold `t' : ℝ≥0ˣ` and a compact set `Ω' ⊆ G(𝔸)`,

such that for every `a` in the intrinsic positive torus `A_{T₀}`
(`PositiveRealTorus.intrinsicSubgroup F T₀`) and every `x ∈ G(𝔸)` with
`IsSiegelPoint F G T i ν T₀ j C t Ω a x` there is `a'` in `A_{T₀'}` with

- `IsSiegelPoint F G T' i' ν' T₀' j' C' t' Ω' a' (q * x)`, and
- `siegelModulus F G T' i' ν' T₀' j' a' = siegelModulus F G T i ν T₀ j a`.

`IsSiegelPoint … C t Ω a x` says `x = z · (n m a k) · w` with `z ∈ A_G`, `n ∈ Ω_N`, `m ∈ Ω_M`,
`a` in the weak simple-root chamber `|β(a)| ≥ t` of the setup, `k` in the compact subgroup of
`C` and `w ∈ Ω`. The modulus `siegelModulus a = ∏_{β ∈ Φ⁺} |β(a)|^{m_β} = δ_{P₀}(a)` is the
modulus of the standard minimal parabolic of the setup at the torus coordinate `a`. In words:
the left translate by one rational point of a Siegel set of the first setup lies in a Siegel set
of the second setup, and the moduli at corresponding torus coordinates agree. The point `q`,
the factors `C'`, the threshold `t'` and the set `Ω'` depend on the two setups and on
`(C, t, Ω)`, not on `a` or `x`.

A typical use: a function on `G(𝔸)` that is left `G(F)`-invariant and is bounded on the Siegel
sets of one setup by `B · δ'(a')^{1/2}` times a power of a height satisfies a bound of the same
form on the Siegel sets of every other setup, since `δ'(a') = δ(a)` and the height of `q x` is
bounded by a fixed multiple of the height of `x`. The theorem
`weakConstantTermLeviSiegelBound_of_reduction` (module
`Langlands.Global.AdelicWeakConstantTermLeviSiegelBound`) uses the statement in this way for
the Siegel sets of a standard Levi subgroup.

## Sources

- A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), 55–150, registered as
  `borel-tits-1965-groupes-reductifs` (printed page numbers):
  - Proposition 4.7, p. 88: for `k`-parabolic subgroups `P, P'`, the group `P ∩ P'` has
    `k`-Levi subgroups, and any two of them are conjugate by a unique element of
    `R_u(P ∩ P')(k)`;
  - Théorème 4.13 b), p. 90: two minimal `k`-parabolic subgroups are conjugate over `k`;
  - Corollaire 4.16, pp. 91–92: for a minimal `k`-parabolic `P`, the `k`-Levi subgroups of `P`
    are the centralizers of the maximal `k`-split tori of `G` contained in `R(P)`, and every
    maximal `k`-split torus of `G` contained in `P` lies in `R(P)`;
  - Théorème 4.21, p. 93: maximal `k`-split tori of `G` are conjugate over `k`; its proof
    conjugates a pair (minimal parabolic, Levi subgroup) by 4.13 and 4.7 and recovers the
    torus as the largest `k`-split torus of the centre of the Levi subgroup.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`: I.2.1, printed pp. 18–20, the
  Siegel domains `S = {p a k : p ∈ ω, a ∈ A_{M₀}(t₀), k ∈ K}` attached to the fixed minimal
  parabolic `P₀` and its Levi subgroup `M₀`.
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
  `delorme-2023-spectral-theorem-langlands` (published PDF numbering), §2, (2.3), p. 7: Siegel
  domains `𝔰_G` of `G(𝔸)` attached to the fixed minimal parabolic.

## Provenance (derived)

The sources define Siegel sets for one fixed minimal parabolic `P₀` and a fixed Levi subgroup of
it; the statement compares the Siegel sets of two such choices. The comparison rests on the
following facts.

*Conjugating the algebraic data.* In a setup `(T, i, ν, T₀, j)` the torus `T` is a maximal
`F`-split torus of `G`, the standard parabolic `P₀ = P(ν)` of the generic cocharacter `ν` is a
minimal `F`-parabolic containing `T`, its Levi subgroup is `M₀ = Z_G(T)`, and its relative roots
are the positive roots of `ν`. By Théorème 4.13 b) there is `q₁ ∈ G(F)` with
`q₁ P₀ q₁⁻¹ = P₀'`. The tori `q₁ T q₁⁻¹` and `T'` are maximal split tori of `G` contained in
`P₀'`, hence in `R(P₀')`, and their centralizers are `F`-Levi subgroups of `P₀'`
(Corollaire 4.16); by Proposition 4.7 these are conjugate by some `u ∈ R_u(P₀')(F)`, and then
`u q₁ T q₁⁻¹ u⁻¹ = T'`, both being the largest split torus of the centre of the common Levi
subgroup (as in the proof of Théorème 4.21). The Library's `minimalParabolicConjugacy` and
`minimalParabolicSplitTorusConjugacy` prove the scheme-theoretic forms of these two steps. With
`q = u q₁`, conjugation `Int(q)` carries `P₀, T, M₀, N₀` onto `P₀', T', M₀', N₀'`, induces an
isomorphism `T ≅ T'` that maps the relative roots of `P₀` (the positive roots of `ν`) onto
those of `P₀'` (the positive roots of `ν'`), hence simple roots onto simple roots, and preserves
the dimensions `m_β` of the weight spaces on the Lie algebra. Since the image of `T₀` is the
largest split torus of `T ∩ D`, with `D` the derived subgroup, `Int(q)` also induces an
isomorphism `T₀ ≅ T₀'` compatible with `j` and `j'`.

*Transporting Siegel points.* Let `x = z · n m a k · w` be a Siegel point of `(C, t, Ω)`. The
point `z ∈ A_G` is central, so `q x = z · (q n q⁻¹)(q m q⁻¹)(q a q⁻¹)(q k q⁻¹) · (q w)`. Here
`q n q⁻¹` lies in the image of `Ω_N` in `N₀'(𝔸)`, `q m q⁻¹` in the image of `Ω_M` in the
norm-one group of `M₀'`, `q a q⁻¹ = a'` is the image of `a` under `A_{T₀} ≅ A_{T₀'}`, which
satisfies `|β'(a')| = |β(a)|` for corresponding roots, `q k q⁻¹` lies in the compact subgroup
`q K q⁻¹`, and `q w ∈ q Ω`. So `q x` is a Siegel point of the second setup for the conjugated
compact factors `C'`, the same threshold `t' = t` and `Ω' = q Ω`, with torus coordinate `a'`,
and `δ'(a') = ∏_{β'} |β'(a')|^{m_{β'}} = ∏_β |β(a)|^{m_β} = δ(a)`. The statement asserts only
the existence of such `q`, `C'`, `t'`, `Ω'` and `a'`.
