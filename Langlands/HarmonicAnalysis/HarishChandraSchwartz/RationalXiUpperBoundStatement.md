# The upper bound of Waldspurger's Lemma II.1.1 for the actual `Ξ` (statement)

Author: Worker 3642 (formerly Worker 19), task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927`
(revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLowerBound`. It uses that module's
companion `RationalWeights` for `rationalMinimalModulus` (`δ₀`), `rationalXi` (`Ξ`) and
`rationalHeight` (`σ`), and for the local instances `rationalWeightsTopology` etc. These put the
canonical rational-point topology `rationalPointTopology F G.X` and the Borel structure on
`G(F) = rationalPoints G`. Through its imports it also uses `SimultaneousStandardBasisAt`,
`IsCompatibleStandardSplitComponent`, `standardComponentCAplus`
(`Langlands.BruhatTits.SpecialCompact`), `IsGenericCocharacter`, `IsMaximalSplitTorus`,
`IsConnectedReductive`, `MatrixRepresentation`, `IsClosedSubgroup`, and the abstract
`XiUpperBound` and `iwasawaWeight` (`SphericalBounds`, `Spherical`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The quotations below were checked against the
rendered PDF pages.

- I.1, printed p. 240: "On définit `M̄_0^+ = H_{M_0}^{-1}(ā_0^+)`, `Ā_0^+ = M̄_0^+ ∩ A_0`", where
  `H_M` is defined by "`q^{-⟨χ, H_G(g)⟩} = |χ|_F(g)` pour tout `χ ∈ Rat(G)`". So
  `m ∈ M₀` lies in `M̄_0^+` exactly when `|α(m)|_F ≤ 1` for every simple root `α`.
- I.1, printed p. 242: "Fixons un plongement algébrique `τ : G → GL_n(F)`. [...] posons
  `‖g‖ = sup_{i,j} sup(|a_{ij}|_F, |b_{ij}|_F)`" (the entries of `τ(g)` and `τ(g)^{-1}`), and
  "On pose `σ(g) = log ‖g‖`."
- II.1, printed pp. 250–251: "`(π, V) = (I_{P_0}^G 1, I_{P_0}^G ℂ)`, `e` l'unique élément de `V`
  invariant par `K` et tel que `e(1) = 1`. [...] Pour `g ∈ G`, on pose `Ξ(g) = ⟨π(g)e, e⟩`." and
  "On a l'égalité: `Ξ(g) = ∫_K δ_0(m_0(kg))^{1/2} dk`."
- Lemme II.1.1, printed p. 251: "La fonction `Ξ` est bi-invariante par `K`. Il existe
  `C_1, C_2 > 0` et `d ∈ ℕ` tels que pour tout `m ∈ M̄_0^+`, on ait
  `C_1 δ_0(m)^{1/2} ⩽ Ξ(m) ⩽ C_2 δ_0(m)^{1/2}(1 + σ(m))^d`."
- Lemme II.1.2, printed p. 251: "Il existe `d ∈ ℕ` et, pour tous `g_1, g_2 ∈ G`, il existe `C > 0`
  tels que, pour tout `g ∈ G`, on ait `Ξ(g_1 g g_2) ⩽ C Ξ(g)(1 + σ(g))^d`." Its proof begins: "Le
  même raisonnement que dans la démonstration précédente prouve l'existence de `d ∈ ℕ` et `C > 0`
  tels que `Ξ(g_1 k_1 m k_2 g_2) ⩽ C δ_0(m)^{1/2}(1 + σ(m))^d` pour tout `m ∈ M̄_0^+`. On peut
  choisir `d` indépendamment de `g_1, g_2, k_1, k_2` et `C` indépendamment de `k_1` et `k_2`."

The present statement is the second inequality of Lemma II.1.1 in this uniform form, with
`k₁ = k₂ = 1`.

## The statement

`RationalXiUpperBoundStatement.{u}` (a `Prop`) asserts the following. Take

- a nonarchimedean local field `F : Type u` (`[IsNonarchimedeanLocalField F]`, any
  characteristic);
- a group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]`
  and `IsConnectedReductive G` (no split or quasi-split hypothesis);
- a maximal split torus `i : S → G` (`IsMaximalSplitTorus i`);
- a generic cocharacter `ν` (`IsGenericCocharacter i ν`: `ν` pairs nontrivially with every
  relative root). It fixes the positive system, the minimal standard parabolic
  `P₀(F) = standardParabolicPoints i ν ∅` and its radical `U₀(F)`;
- a subgroup `K0` of `G(F)` with `SimultaneousStandardBasisAt i ν K0` (structural hypothesis, see
  below);
- a compatible split component `q : A → S` of `M₀` (`IsCompatibleStandardSplitComponent i ν ∅ A q`);
- a subgroup `K` of `G(F)` that is open and compact (`hKc`) with `G(F) = P₀(F) K`
  (`hPK : IsIwasawaPair P₀(F) K`);
- a matrix representation `ρ : G → GL_N` (`N ≥ 1`) that is a closed immersion
  (`IsClosedSubgroup ρ`).

Then there is `d : ℕ` such that for all `g₁, g₂ ∈ G(F)` there is `C : ℝ` with

`rationalXi hKc hPK (g₁ * a * g₂) ≤ C * δ₀(a)^{1/2} * (1 + rationalHeight ρ a)^d`

for every `a ∈ P₀(F)` (`ha`) in the weak chamber `standardComponentCAplus i ν ∅ q`. Here
`δ₀(a) = rationalMinimalModulus i ν ⟨a, ha⟩` and `δ₀(a)^{1/2}` is `NNReal.sqrt`.

### Correspondence with the source

- `Ξ`: `rationalXi hKc hPK` is the Library's `xi` for `P₀(F)` and `δ₀`:
  `Ξ(g) = ∫_K δ₀(p(kg))^{1/2} dk` with the Haar probability measure on `K`. Here `kg = p(kg) k'`
  with `p(kg) ∈ P₀(F)` and `k' ∈ K`. `RationalXiLowerBound.md` explains when the integrand is
  Waldspurger's `δ₀(m₀(kg))^{1/2}`. Waldspurger takes `K` to be the fixer of a special point. The
  statement allows any compact open `K` with `G(F) = P₀(F) K`. For such `K`, `Ξ` is again the
  coefficient `⟨π(g)e_K, e_K⟩` of `I_{P₀}^G 1` at its vector `e_K(pk) = δ₀(p)^{1/2}`, so the
  source's argument applies. This identification is mathematical background, not a Lean result.
- `δ₀`: the Haar modulus of the conjugation action of `P₀(F)` on `U₀(F)`
  (`μ(p E p⁻¹) = δ₀(p) μ(E)`). For connected reductive `G` this agrees with Waldspurger's
  `δ_0 = δ_{P_0}` on `M₀(F)` by the standard identification of the modulus of `P₀` on its Levi
  with the modulus of conjugation on `U₀` (background, not proved here). On the chamber,
  `|α(a)|_F ≤ 1` for the simple roots, so `a` contracts `U₀(F)` under conjugation and
  `δ₀(a) ≤ 1`.
- `σ`: `rationalHeight ρ g = log ‖ρ(g)‖`, where `‖·‖` is the largest normalized absolute value of
  an entry of `ρ(g)` or `ρ(g)⁻¹`. This is Waldspurger's `σ` for the embedding `τ = ρ`.
  Waldspurger also assumes `τ(K) ⊂ GL_n(𝒪)`. That assumption is not made here. It only makes `σ`
  bi-invariant under `K`. The heights of two closed embeddings bound each other affinely
  (background, not proved here), so the assumption does not change the content of the bound.
- The chamber: `standardComponentCAplus i ν ∅ q` is the set of images in `G(F)` of the points
  `c(ϖ)` (`c` a cocharacter of `A`, `ϖ` the Library's common uniformizer) whose values on all
  simple characters have absolute value at most `1`. This is the lattice part of Waldspurger's
  `Ā_0^+ = M̄_0^+ ∩ A_0`. It is the same set as in the published lower bound
  `exists_sqrt_rationalMinimalModulus_le_rationalXi` of `RationalXiLowerBound`.
- Uniformity: `d` is chosen before `g₁, g₂`, and `C` may depend on `g₁, g₂`, as in the proof of
  Lemma II.1.2. With `g₁ = g₂ = 1` this is the upper bound of Lemma II.1.1 on the chamber.

### Structural hypothesis

`SimultaneousStandardBasisAt i ν K0` is Renard's V.5.2 basis property for all standard
parabolics at `K0`. It gives a compact open normal basis with ordered Iwahori factorizations and
the contraction and cofinality clauses for compatible split components (rows S20–S23 of
`notes/renard/chapter-v-structural-inputs.md`). The Library does not prove it in general. The
unproved structural `JointSpecialCompactBasisExistenceStatement` asserts it, for generic `ν`, at
the special compact subgroup of a special vertex. The statement is therefore conditional on this
external Chapter V input. Waldspurger's route to the bound goes through Proposition I.4.3, which
rests on compact open subgroups of this kind. The Library's actual Theorem I.4.1 for standard
parabolics,
`exists_standardCasselmanPairing` in `StandardCasselmanPairing`, takes basis members of this
kind as input.
The upper bound itself does not mention `K0`, and `K` need not be related to `K0`.

## Supporting results

- `mem_standardParabolicPoints_of_mem_standardComponentCAplus`: for a compatible split component of
  `M_J`, every point of the weak chamber `standardComponentCAplus i ν J q` lies in
  `standardParabolicPoints i ν J`. Proof: the chamber points are images of points of `A(F)`. These
  lie in `M_J(F)` (the Library's `IsCompatibleStandardSplitComponent.map_mem_standardLeviPoints`),
  and `M_J(F) ⊆ P_J(F)`.
- `RationalXiUpperBoundStatement.xiUpperBound`: from the statement, with the same data, the
  Library's abstract
  `XiUpperBound (rationalXi hKc hPK) (rationalHeight ρ) (standardComponentCAplus i ν ∅ q)
  (iwasawaWeight hPK (rationalMinimalModulus i ν))`, that is `∃ C d : ℝ`,
  `Ξ(a) ≤ C φ(a) (1 + σ(a))^d` on the chamber, with `φ(p k) = δ₀(p)^{1/2}`. Proof: take
  `g₁ = g₂ = 1`. Then `φ(a) = φ(a · 1) = δ₀(a)^{1/2}` for `a ∈ P₀(F)` (`iwasawaWeight_mul`, with
  `δ₀` trivial on `P₀(F) ∩ K` by `rationalMinimalModulus_eq_one`), and the natural power equals
  the real power (`Real.rpow_natCast`). This is the form taken as a hypothesis by the Library's
  abstract estimates (for example `XiUpperBound.univ_of_cartan` and the consumers in
  `CuspidalDecay`, `ConjugationBound` and `LevelSetBound`).

## Status and scope

This is a statement target; it is not proved here. Waldspurger's proof fixes `t` as in
Proposition I.4.3 for the pair `(e, e)`. It splits `M̄_0^+` into the regions `M̄_0^+(P)` of the
standard parabolics `P`, and uses that `(π_P(a) − 1)^d` kills the Jacquet module `V_P` of
`I_{P_0}^G 1` for `a ∈ A_M` ("On sait calculer `π_P`, cf. I.3"). So the coefficient of the
Jacquet module is a polynomial in `H_M(a)`. A proof along this route needs, for the actual group:

1. the identification of `rationalXi` with a coefficient of the actual normalized induction
   `I_{P₀}^G 1`;
2. Proposition I.4.3 for standard parabolics, uniformly on the chamber, built on the actual
   Theorem I.4.1 `exists_standardCasselmanPairing` and a basis as in
   `SimultaneousStandardBasisAt`;
3. the exponents of the Jacquet modules of `I_{P₀}^G 1`, which come from the geometric lemma.

The statement does not cover all of `M̄_0^+`. The extension to `M̄_0^+` uses that `M̄_0^+` lies
in the chamber times a compact subset of `M₀(F)`, together with the uniformity in `g₁, g₂`; it
is not derived here. The lower bound of Lemma II.1.1 is the published
`rationalXi_lowerBound`, which does not use the structural hypothesis.
