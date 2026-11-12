# Corollary III.1.2 and III.7 of Waldspurger on actual rational points

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay`,
namespace `Langlands.HarishChandraSchwartz`.

The module concerns the spherical function `Ξ = rationalXi` and the height `σ = rationalHeight ρ`
of the Library's `RationalWeights` on the actual rational points `G(F)` of a connected reductive
group. It contains:

- the statement `RationalSquareIntegrableRapidDecayStatement` of Corollary III.1.2: the
  coefficients of a representation that is square integrable modulo `A_G(F)` decrease rapidly
  on `G¹` relative to `Ξ` and `σ`. It is conditional on the same two structural inputs from
  Renard Chapter V as the published Lemma II.1.5 statement;
- a proof of Lemma II.1.2 for the actual `Ξ` and of the translation bound for `σ`, which together
  give the Library's `TranslationWeights` for the actual weights;
- a proof that rapid decay does not depend on the closed matrix representation defining `σ`;
- a proof of the second paragraph of III.7 on actual points: a coefficient whose coefficients
  decrease rapidly on `G¹`, multiplied by a compactly supported function on `G(F)/G¹`, lies in
  `C(G)`. Combined with the statement, this gives III.7 for square-integrable representations.

The recorded declaration is the statement `RationalSquareIntegrableRapidDecayStatement`. It is a
proposition definition, not a proof.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers below are the
printed ones; the PDF page is the printed page minus 234. The author checked the quotations
against the text of PDF pages 5, 17, 29, 30 and 39.

- I.1, printed p. 239: "On pose `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`"; `A_G` is the largest split torus
  in the center of `G`.
- Lemme II.1.2, printed p. 251: "Il existe `d ∈ ℕ` et, pour tous `g₁, g₂ ∈ G`, il existe `C > 0`
  tels que, pour tout `g ∈ G`, on ait `Ξ(g₁ g g₂) ⩽ CΞ(g)(1 + σ(g))^d`."
- III.1, printed p. 263: "Soit `(π, V)` une représentation admissible de `G` admettant un
  caractère central unitaire. On dit que `π` est de carré intégrable si tous les coefficients de
  `π` sont de carré intégrable sur `A_G \ G`."
- Corollaire III.1.2, printed p. 263: "Supposons `π` de carré intégrable. Alors pour tout
  `f ∈ A(π)` et tout `r ∈ ℝ`, il existe `c > 0` tel que pour tout `g ∈ G¹`, on ait l'inégalité
  `|f(g)| ⩽ cΞ(g)(1 + σ(g))^{−r}`."
- Its proof, printed p. 264: "On peut supposer `f` de la forme `f(g) = ⟨π(g)v, v̌⟩` pour des
  éléments `v ∈ V`, `v̌ ∈ V̌`. Grâce à I.1 (4) et à un argument de `K`-finitude, on peut se limiter
  à démontrer l'inégalité pour `g ∈ M̄₀⁺ ∩ G¹`. Un argument analogue à celui de la preuve du
  Lemme II.1.1 nous conduit à fixer un sous-groupe parabolique standard `P = MU` de `G`, des
  éléments `v_P ∈ V_P` et `v̌_{P̄} ∈ (V̌)_{P̄}` et à majorer la fonction
  `a ↦ δ_P(a)^{1/2} ⟨π_P(a)v_P, v̌_{P̄}⟩_P` (1) pour `a ∈ Ā₀⁺ ∩ A_M ∩ G¹`." The proof then uses
  Lemma II.1.1 (`δ_P(a)^{1/2} ⩽ C₁Ξ(a)`), a polynomial bound
  `|Q_χ(H_M(a))| ⩽ C₂(1 + σ(a))^d`, and Proposition III.1.1 (Casselman's criterion,
  [C, Théorème 4.4.6]: `Re(χ) ∈ ⁺a_P^{G*}` for every exponent `χ`), which gives
  `|χ(a)| ⩽ C₃q^{−εσ(a)}`.
- III.7, printed p. 273: "Soient `(ω, E)` une représentation admissible de carré intégrable de
  `G`, `f ∈ A(ω)` et `ϕ ∈ C_c(G/G¹)`. Il résulte du Corollaire III.1.2 que la fonction produit
  `fϕ` appartient à `C(G)`."

Renard, *Représentations des groupes réductifs p-adiques* (2026), V.5.1 and V.5.2, as itemized in
the Library's note `notes/renard/chapter-v-structural-inputs.md`: row S19 (V.5.1, including the
Cartan decomposition (4)) and rows S20–S23 (V.5.2, the simultaneous standard basis).

## Setting

`F` is a nonarchimedean local field of any characteristic. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`. `G(F) = rationalPoints G`
carries the canonical topology `rationalPointTopology F G.X` and its Borel σ-algebra (the local
instances of `RationalWeights`), with second countability, the Hausdorff property and the
nonarchimedean group property (`Plancherel.rationalPoints_nonarchimedeanGroup`). For `i : S → G`
and a cocharacter `ν`, `P₀(F) = standardParabolicPoints i ν ∅`. `K` is a subgroup of `G(F)` with
`hKo : IsOpen K`, `hKc : IsCompact K` and `hPK : IsIwasawaPair P₀(F) K` (`G(F) = P₀(F) K`).
`Ξ = rationalXi hKc hPK` and `σ = rationalHeight ρ` for a matrix representation `ρ`.
`G¹ = Plancherel.rationalCommonNormKernel G`, the intersection of the kernels of `|χ|_F` over the
rational characters `χ` of `G`; it is open (`Plancherel.isOpen_rationalCommonNormKernel`) and
normal.

The Library's predicates used are:

- `IsRapidlyDecreasingOn Ξ σ L f` (module `CoefficientCutoff`): for every `r ∈ ℝ` there is a real
  `c` with `‖f(n)‖ ≤ c Ξ(n) (1 + σ(n))^{-r}` for all `n ∈ L`.
- `HasRapidlyDecreasingCoefficientsOn Ξ σ L π` (same module): every coefficient
  `g ↦ ℓ(π(g) v)`, with `v` a vector and `ℓ` a smooth functional, satisfies
  `IsRapidlyDecreasingOn Ξ σ L`.
- `Plancherel.IsSquareIntegrableModCentralSubgroup A hA π μ` (module
  `Representation.Plancherel.CentralSubgroupCoefficients`), for a central normal subgroup `A`:
  `π` is admissible, it has a unitary central character `c` (a character of the full center of
  `G(F)` with open kernel and modulus one by which the center acts), and for every smooth
  functional `ℓ` and vector `v` the function `gA ↦ ‖ℓ(π(g) v)‖` on `G(F)/A` lies in `L²(μ)`. With
  `A` the image `A_G(F)` of a split component, this is the predicate defining the Library's
  discrete-series classes `DiscreteSeriesClass` (Waldspurger's `E₂(G)`).

## Corollary III.1.2 (statement)

**`RationalSquareIntegrableRapidDecayStatement`** (universes `u` for the field and `uV` for the
representation carriers): for every universe-`u` nonarchimedean local field `F`, every
connected reductive `G` (`IsConnectedReductive G`), maximal split torus `i`
(`IsMaximalSplitTorus i`), generic cocharacter `ν` (`IsGenericCocharacter i ν`), and every
subgroup `K0` of `G(F)` such that

- `K0` is open and compact,
- `SimultaneousStandardBasisAt i ν K0` holds (Renard V.5.2), and
- `Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0` holds (the covering clause of
  Renard V.5.1 (4): a finite set `F₀` of points of the torus centralizer with
  `G(F) = ⋃ K0 f a K0`, `f ∈ F₀`, `a` in the dominant uniformizer chamber `C_A^+` of `S(F)`),

and for every compact open `K` with `G(F) = P₀(F) K`, every `N ≥ 1`, every closed matrix
representation `ρ : G → GL_N` (`IsClosedSubgroup ρ`), every split component `s : T → G`
(`IsSplitComponent s`, with image `A_G(F) = (rationalPoints.map s).range`, a closed central
subgroup of `G(F)`), every Haar measure `mu` on `G(F)/A_G(F)` (Borel σ-algebra of the quotient
topology) and every smooth representation `A : SmoothRep ℂ G(F)`:

if `Plancherel.IsSquareIntegrableModCentralSubgroup A_G(F) _ A.representation mu`, then
`HasRapidlyDecreasingCoefficientsOn Ξ σ G¹ A.representation`, i.e. for every vector `v`, smooth
functional `ℓ` and `r ∈ ℝ` there is `c` with `|ℓ(π(g) v)| ≤ c Ξ(g) (1 + σ(g))^{-r}` for all
`g ∈ G¹`.

### Correspondence with the source

- Square integrability is Waldspurger's definition of III.1: admissible, a unitary central
  character, and square-integrable coefficients on `A_G \ G`. Here `A_G(F)` is the image of a split
  component (any one: the statement quantifies over all of them) and `mu` is any Haar measure on
  the quotient; square integrability does not depend on its normalization.
- The conclusion is stated for the pure coefficients `g ↦ ℓ(π(g) v)`. The source states it for
  every `f ∈ A(π)`, the span of the coefficients. The two forms are equivalent, since rapid decay
  is stable under sums (`IsRapidlyDecreasingOn.add`, and `isRapidlyDecreasingOn_coefficientTensorMap`
  for the whole range of the coefficient map); the source's proof starts with the same reduction.
  The source asks for `c > 0`; a real `c` is equivalent, since `c` may be enlarged.
- The source fixes a special maximal compact `K` and an embedding with `τ(K) ⊂ GL_n(𝒪)`. The
  statement allows every compact open `K` with `G(F) = P₀(F) K` and every closed `ρ`, as the
  published `RationalXiSquareIntegrableStatement` does. The conclusion remains true in this
  generality. For the height, `hasRapidlyDecreasingCoefficientsOn_rationalHeight_iff` below
  proves the independence of `ρ`. For `K`, the functions `Ξ_K` attached to two such subgroups are
  bounded by constant multiples of each other (both are coefficients of `I_{P₀}^G 1` for positive
  `P₀`-covariant vectors and positive functionals; `P₀(F) \ G(F)` is compact); this comparison is
  not formalized.
- The structural premises are the external inputs of the source's proof: the Cartan
  decomposition I.1 (4) for the reduction to `M̄₀⁺ ∩ G¹`, and Renard's V.5.2 basis for
  Proposition I.4.3 (the "argument analogue à celui de la preuve du Lemme II.1.1") and the lower
  bound of Lemma II.1.1. `K0` is assumed compact open, so that the covering clause is not
  trivially satisfied by `K0 = G(F)`. The representation-theoretic inputs of the proof
  (Proposition I.4.3, the exponents of the Jacquet modules, Casselman's criterion III.1.1) are not
  premises; they are obligations of a proof.
- The statement quantifies over all connected reductive group schemes, so it applies in
  particular to Levi subgroups viewed as group schemes. The comparison with the actual standard
  Levi subgroups `M_J(F) = standardLeviPoints i ν J` and their `Ξ^{M_J} = rationalLeviXi` (module
  `RationalXiLevi`), which Lemma VI.2.2 needs, is not formalized here.

### Inputs available for a proof

- Lemma II.1.1, lower bound on the weak chamber: `rationalXi_lowerBound` (module
  `RationalXiLowerBound`, proved from one basis member).
- Proposition I.4.3 for the standard parabolics, uniformly on dominant points:
  `SimultaneousStandardBasisAt.exists_waldspurger_uniform_asymptotics` (module
  `Representation.Jacquet.StandardCasselmanUniformAsymptotics`).
- The abstract last step of the proof: `isRapidlyDecreasingOn_of_cartan` and
  `exists_rpow_bound_of_exp_bound` (module `CoefficientRapidDecay`) reduce rapid decay to
  exponential bounds on finitely many pieces of the positive chamber.
- Casselman's criterion on actual rational points: the Library has the statement
  `ArbitraryParabolicCasselmanCriterionStatement` (Renard VII.1.2 for represented parabolics,
  unproved; module `Representation.Exponents.ArbitraryParabolicCasselmanStatement`) with square
  integrability modulo the full center. Its comparison with the standard parabolics `P_J` and with
  square integrability modulo `A_G(F)` is not formalized.
- The one-sided I.1 (6) bound `RationalUniformizerCoordinateHeightStatement` (proved).

## Lemma II.1.2 and translation weights (section `Translation`, proved)

- `rationalXi_uniformTranslationBound hKo hKc hPK`: for all `g₁, g₂` there is `C` with
  `Ξ(g₁ g g₂) ≤ C Ξ(g)` for all `g` (the Library's `UniformTranslationBound`). This is Lemma
  II.1.2 with `d = 0`, a stronger form than the source's. It is the Library's generic
  `xi_uniformTranslationBound` (module `SphericalTranslation`), whose proof uses Lemma II.1.3 and
  the bi-`K`-invariance of `Ξ`, applied with `δ₀ = 1` on `P₀(F) ∩ K`
  (`rationalMinimalModulus_eq_one`) and the openness of `K`. No structural hypothesis and no
  reductivity is needed.
- `rationalHeightTranslationBound ρ`: for all `g₁, g₂` there is `C` with
  `1 + σ(g₁ g g₂) ≤ C (1 + σ(g))`, from the subadditivity `rationalHeight_mul_le` through the
  generic `heightTranslationBound_of_le_add`.
- `rationalTranslationWeights hKo hKc hPK ρ`: the Library's `TranslationWeights Ξ σ`
  (`Ξ > 0` by `rationalXi_pos`, `σ ≥ 0`, Lemma II.1.2, and the translation bound for `σ`). These
  are the hypotheses of the Library's generic translation results (module `Translations` and
  `CoefficientCutoff`).

## Independence of the matrix representation (proved)

- `rpow_le_rpow_abs_mul_of_le`: for `x, y > 0` and `D ≥ 1` with `x ≤ D y` and `y ≤ D x`,
  `y^t ≤ D^{|t|} x^t` for every real `t`.
- `IsRapidlyDecreasingOn.of_one_add_le`: if `Ξ ≥ 0`, `σ, σ' ≥ 0`, `1 + σ' ≤ C (1 + σ)` and
  `1 + σ ≤ C (1 + σ')`, then rapid decay on `L` for `σ'` implies rapid decay on `L` for `σ`.
- `hasRapidlyDecreasingCoefficientsOn_rationalHeight_iff hKc hPK ρ ρ' hρ hρ' L A`: for closed
  matrix representations `ρ, ρ'`, every subgroup `L` and every smooth representation `A`,
  `HasRapidlyDecreasingCoefficientsOn Ξ σ_ρ L A.representation` holds if and only if it holds for
  `σ_{ρ'}`. The comparison `1 + σ_τ ≤ C (1 + σ_ρ)` for closed `ρ` is the published
  `exists_one_add_rationalHeight_le` (module `RationalTemperedInduction`, from the Library's
  `rationalMatrixNormComparison`).

## III.7 on actual points (proved)

- **`mul_mem_rationalSchwartz hKo hKc hPK ρ hD hf hφ`**: let `A` be a smooth representation of
  `G(F)` with `hD : HasRapidlyDecreasingCoefficientsOn Ξ σ G¹ A.representation`, let
  `f : LocallyConstant G(F) ℂ` with
  `hf : f ∈ LinearMap.range (Plancherel.coefficientTensorMap A)` (that is, `f ∈ A(π)`, the span of
  the coefficients; the Library's `range_coefficientTensorMap`), and let
  `φ : G(F) ⧸ G¹ → ℂ` with `hφ : HasCompactSupport φ` (that is, `φ ∈ C_c(G/G¹)`; as `G¹` is open,
  the quotient is discrete and `φ` has finite support). Then `g ↦ f(g) φ(g G¹)` lies in
  `schwartzSubmodule Ξ σ`, the underlying space of `RationalSchwartzSpace` (`C(G)`). The proof is
  the Library's generic `TranslationWeights.mul_mem_schwartzSubmodule` (module
  `CoefficientCutoff`), applied with `rationalTranslationWeights`, the openness of `G¹`, and the
  compact open subgroup `K` (which supplies `Nonempty (CompactOpenSubgroup G(F))`).
- `RationalSquareIntegrableRapidDecayStatement.hasRapidlyDecreasingCoefficientsOn`: the statement
  applied to one group, under its structural hypotheses.
- **`RationalSquareIntegrableRapidDecayStatement.mul_mem_rationalSchwartz`**: III.7 for actual
  square-integrable representations. Given the statement and its structural hypotheses, for every
  `A` with `IsSquareIntegrableModCentralSubgroup A_G(F) _ A.representation mu`, every `f ∈ A(π)`
  and every compactly supported `φ` on `G(F)/G¹`, `f φ ∈ C(G)`. This is the sentence of III.7
  with Corollary III.1.2 as an explicit premise.

## Scope

- Corollary III.1.2 is not proved here. A proof needs the representation-theoretic inputs listed
  above, some of which are unproved statements.
- The consequence "toute représentation de carré intégrable est tempérée" (III.2, printed p. 265),
  which needs the passage from `G¹` to `G(F)` (finiteness of `G(F)/G¹A_G(F)` and the central
  character), is not treated.
- The existence of a special `K` and of `K0` with the two structural properties is not proved
  here. In the Library they are among the clauses of the unproved
  `JointSpecialCompactBasisExistenceStatement` and `IwasawaExistenceStatement`.
- Provenance: the statement is a direct translation of Corollary III.1.2 with the structural
  premises displayed, with the generalizations in `K` and `ρ` explained above.
  `rationalXi_uniformTranslationBound` is Lemma II.1.2 (with `d = 0`) through the Library's
  generic `SphericalTranslation`. `mul_mem_rationalSchwartz` and its statement form are III.7
  through the Library's generic `CoefficientCutoff`. The remaining declarations are internal glue.
