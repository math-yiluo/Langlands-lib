# Finite expansions of intertwining operators on `A^2_P` in `A^2_Q`

Module `Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement`
states one proposition,
`Langlands.Global.IntertwiningSquareIntegrableExpansionStatement`. It proves
nothing and asserts nothing. The proposition is a premise of the bridge
`Langlands.Global.SymmetricFamilyGramBridgeStatement` (module
`Langlands.Global.AdelicSymmetricFamilyGram`). The bridge derives the Gram
identity for wave packets of Arthur's space `L̂` from Lapid's inner product
formula `Langlands.Global.WavePacketInnerProductStatement`.

## Statement

The data are those of `WavePacketInnerProductStatement` (module
`Langlands.Global.AdelicWavePacketInnerProductStatement`), with the second
parabolic named `Q = M'V` instead of `P' = M'U'`:

- a number field `F : Type` and a connected reductive group `G` over `F`;
- a parabolic `p : P → G` with unipotent radical `iU : U → P`, rational Levi
  `l : M → P` and presentation `r : ParabolicRootPresentation p l a`
  (`hA`, `hT` say that the tori are split);
- a second parabolic `q : Q → G` with unipotent radical `iV : V → Q`, Levi
  `l' : M' → Q` and presentation `r' : ParabolicRootPresentation q l' a'`.
  As in `WavePacketInnerProductStatement`, the presentation `r'` stands for
  the hypotheses `IsParabolicSubgroup q` and `IsRationalLeviSubgroup l'` of
  `Langlands.Global.IntertwiningMeromorphicContinuationStatement`. In
  addition, `Q = M' ⋉ V` (`IsIso (subgroupMultiplication l' iV)`), and
  `π' : Q → M'` satisfies `l' ≫ π' = 𝟙 M'`;
- a Weyl conjugation `(w, c)` from `P` to `Q`
  (`IsWeylConjugation p l q l' w c`), so `w ∈ Ω(P, Q)`;
- a maximal compact subgroup `K` of `G(𝔸)` with `P(𝔸)K = Q(𝔸)K = G(𝔸)`
  (`hK : IsIwasawaCompact p K`, `hK' : IsIwasawaCompact q K`), and the data
  `rho` (a closed embedding), `hsmooth` and `hcalc` that define automorphic
  forms.

The conclusion: for every `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`) there
are `k : ℕ`, functions `ψ i` on `G(𝔸)` (`i : Fin k`), functions `coeff i` on
`X^*(P) ⊗ ℂ` and a set `D` such that

- each `ψ i` lies in `A^2_Q` (`IsSquareIntegrableInducedForm` for `q`, `iV`,
  `l'`);
- `D` contains `i(X^*(P) ⊗ ℝ)` (`Set.range (imaginaryParameter F P) ⊆ D`);
- each `coeff i` is meromorphic on `X^*(P) ⊗ ℂ` with domain of holomorphy
  `D`, in every linear coordinate system (`IsMeromorphicInCoordinatesOn`);
- there is `R₀` such that for every `λ` with
  `r.IsRegularParameter hA hT R₀ λ` and every `g ∈ G(𝔸)`,
  `hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g`.

The left side is the intertwining operator `M(w, λ)φ(g)` of module
`Langlands.Global.AdelicIntertwiningOperator`, defined by its integral. The
regularity condition is that of the convergence statements: `R₀ < B(Re λ, α)`
for all roots `α` of `A` in the unipotent radical.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2, p.312 (PDF
page 321), "Working hypothesis". For `φ ∈ A^2_P`, `λ_0 ∈ 𝔞*_{P,ℂ}`, every
`Q` and every `w ∈ Ω(P, Q)`, there are a neighbourhood `N` of `λ_0` and an
integer `m` such that
`[∏_{α ∈ R(T_M, U)} ⟨λ - λ_0, α^∨⟩]^m M(w, λ)φ` is holomorphic on `N`, with
values in a finite-dimensional subspace of `A^2_Q` determined by the `K`- and
`𝔷`-types of `φ`. Lapid writes that these results "are a consequence of
Langlands' theory (cf. [Lan76], [MW95], [Lap08])". On the same page: "for
`λ ∈ i𝔞*_P`, `M(w, λ)` is unitary, hence holomorphic" (cf.
Mœglin–Waldspurger IV.3.12).

## Correspondence with the source

- Finite-dimensional values. The subspace `W ⊆ A^2_Q` of the working
  hypothesis depends only on the `K`- and `𝔷`-types of `φ`, not on `λ_0`. The
  statement takes a spanning family `ψ i` of `W` and writes
  `M(w, λ)φ = ∑ i, coeff i λ • ψ i`. As in
  `IntertwiningMeromorphicContinuationStatement`, linear independence is not
  required.
- Meromorphy. Near every `λ_0` the coefficients in a basis of `W` are
  holomorphic functions divided by a power of a polynomial. They are
  therefore meromorphic on `X^*(P) ⊗ ℂ`, with domain of holomorphy the set `D`
  where `M(w, λ)φ` is holomorphic. This set is open and dense.
- Domain. `D` contains the imaginary axis because `M(w, λ)` is unitary,
  hence holomorphic, for `λ ∈ i𝔞*_P` (Lapid, loc. cit.). This is the only
  difference from `IntertwiningMeromorphicContinuationStatement`
  (Bernstein–Lapid 2024, Theorem 2.3 (3)), which gives a finite expansion in
  `𝒜_Q` with no information on `D`. The other differences are that `φ` and
  the `ψ i` are in the spaces `A^2` instead of `𝒜`.
- Agreement. For `Re λ` sufficiently regular, the intertwining integral
  converges and defines `M(w, λ)φ`. The meromorphic function of the working
  hypothesis is the continuation of this integral, so the expansion holds
  there for every `g`.
- Scope of the parabolics and of `K`. This premise asks for more than the
  source states. Lapid (§2, p.311, PDF page 320) fixes a minimal Levi `M_0`
  and a minimal parabolic `P_0` over `F`, and one maximal compact subgroup
  `K` of `G(𝔸)` in good position with respect to `M_0`. In §2, `P` and `Q`
  are standard parabolic subgroups over `F`, that is, both contain the one
  fixed `P_0` (this convention is explicit in Bernstein–Lapid 2024, §2.1,
  p.190). The working hypothesis is stated in that setting. The premise
  instead allows two independently presented parabolics `P`, `Q` and any
  maximal compact subgroup `K` with `P(𝔸)K = Q(𝔸)K = G(𝔸)`.
  - Parabolics. Each presentation `r`, `r'` makes its own parabolic standard
    with respect to its own minimal parabolic. The two need not be standard
    with respect to one common minimal parabolic, even after conjugating
    both by one element of `G(F)`. An example: take `G = SL₂` over `ℚ`, `P`
    the upper and `Q` the lower triangular Borel subgroup. They share the
    diagonal Levi, and `SO(2) × ∏_p SL₂(ℤ_p)` gives both Iwasawa
    decompositions. Conjugating both by one `γ ∈ G(ℚ)` keeps them distinct.
    Both are minimal, so if both contained one minimal parabolic `P_0`, both
    would equal `P_0`.
  - The Markdown of `IntertwiningMeromorphicContinuationStatement`
    describes a different reduction, for the spaces `𝒜`. It conjugates only
    the target: some `γ ∈ G(F)` takes `Q` to a standard parabolic, the Weyl
    representative `w` is replaced by `γw`, the evaluation point `g` by
    `γg`, and an entire factor `exp⟨(γw)λ, H_{γQγ⁻¹}(γ)⟩` appears. The
    compact subgroup `K` does not change. That reduction is explanatory and
    not proved in the Library. This premise does not use it, and neither
    this premise nor its Markdown shows that the reduction preserves `A^2`
    or holomorphy near the imaginary axis.
  - Compact subgroup. Some compact subgroups allowed here are not in good
    position with respect to any minimal Levi over `F`, even after
    conjugation by `G(F)`. An example: take `G = SL₂` over `ℚ`, `P = Q` the
    upper triangular Borel, `t = ∛2`, `u_t` the upper unipotent matrix with
    entry `t`, and `K = u_t SO(2) u_t⁻¹ × ∏_p SL₂(ℤ_p)`. This `K` is maximal
    compact, and `P(𝔸)K = G(𝔸)` because `u_t ∈ P(ℝ)`. Its Lie algebra is
    spanned by `J_t = [[t, -1-t²], [1, -t]]`. Good position at the real place
    (Arthur 1978, §1, p.917, condition (iii)) asks that the Lie algebra of
    some maximal split torus over `ℚ` be orthogonal to `J_t` for the Killing
    form. That Lie algebra is spanned by a nonzero rational trace-zero matrix
    `X = [[a, b], [c, -a]]`, and orthogonality means
    `2at + b - (1+t²)c = 0`. This forces `X = 0`, because `1, t, t²` are
    linearly independent over `ℚ`. Every maximal split torus over `ℚ` is of
    this kind, so conjugation by `G(ℚ)` does not help.
  - The Markdown of the Eisenstein convergence statement
    (`AdelicEisensteinConvergenceStatement.md`) explains how a change of
    compact subgroup rewrites intertwining integrals for `K` as finite
    combinations, with entire coefficients, of intertwining integrals for a
    compact subgroup `K₀` in good position. That explanation concerns the
    spaces `𝒜_P`. Neither it nor this module shows that the transported
    inducing functions lie in `A^2` for `K₀`. Nor do they show that the
    transported outputs lie in a finite-dimensional subspace of `A^2_Q` for
    `K`, with coefficients holomorphic near the imaginary axis.

  The validity of the expansion for parabolics that are not standard with
  respect to one common minimal parabolic, and for every maximal compact
  subgroup `K` with the Iwasawa decompositions, is therefore
  an additional assumption of this premise. It does not follow from the
  cited source. The bridges that use this premise need this generality
  because their conclusions are stated for every such `K`.

## Provenance

Internal formulation of Lapid's working hypothesis (2011, §2, p.312) for one
pair `(P, Q)` and one `φ`, in the Library's coordinates (`intertwiningOperator`,
`IsSquareIntegrableInducedForm`, `IsMeromorphicInCoordinatesOn`,
`imaginaryParameter`). Lapid states the hypothesis for parabolics standard
with respect to one fixed minimal parabolic, and a fixed `K` in good
position. This premise also assumes it for independently presented
parabolics and for every maximal compact `K` with the Iwasawa
decompositions. That extension is an assumption of the premise, not a result
of the source (see "Scope of the parabolics and of `K`" above). The bridge needs it because
`WavePacketInnerProductStatement` and `IsImaginaryIntertwiningOperator` take
expansions in `A^2_Q` whose domain contains the imaginary axis, and no
published statement provides them. The Library's continuation statement gives
expansions in `𝒜_Q` only. The unitarity statement
`IntertwiningImaginaryUnitarityStatement` starts from an expansion in `A^2_Q`.
It returns new coefficients, holomorphic on the imaginary axis, that agree with
the old ones only on the intersection of the two domains. Recovering
agreement on a whole regular region from this would need the continuity of
`λ ↦ M(w, λ)φ` when `A` has no root in `U`, and the Library does not state it.
