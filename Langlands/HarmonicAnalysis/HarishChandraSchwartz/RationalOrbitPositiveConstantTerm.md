# Weak and positive constant terms of actual orbit coefficients (Waldspurger VI.2.3)

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm`,
namespace `Langlands.HarishChandraSchwartz`.

This module supplies the definitions and the Prop-valued targets for the constant-term split of
the actual induced orbit coefficients `f_ω = E^G_P ψ_ω` that the proof of Waldspurger's
Proposition VI.3.1 uses, and for Lemma VI.2.3. It works on actual rational points of a connected
reductive group `G` over an arbitrary nonarchimedean local field `F` (any characteristic, `G`
not necessarily split or quasisplit), with the shared `GroupScheme`, the canonical rational-point
topology, the actual standard parabolic and Levi subgroups and canonical complex `SmoothRep`
objects. The field universe `u` and the representation universe `uV` stay independent: every
target has level parameters exactly `u, uV`.

The module **proves no estimate**. The uniform threshold, the weak-term limit, the decay
estimate and (optionally) the existence of the constant terms are published as named targets;
their proofs are separate modules (see "Unresolved obligations").

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
numbers; the PDF page is the printed page minus 234. The quotations below were checked against
the text extracted from PDF pages 5, 6, 11, 12, 35, 36, 62–67, 69 and 71.

- **I.1, printed p. 239.** "On fixe un sous-groupe parabolique minimal `P_0` de Lévi `M_0`. On
  pose `Δ_0 = Δ(P_0)`." "On pose `ā_0^+ = {H ∈ a_0 ; ∀α ∈ Δ_0, ⟨α, H⟩ ⩾ 0}`." "Si `P ∈ 𝒫(M)`,
  on note `Σ(P)` le sous-ensemble des racines de `A_M` positives relativement à `P`, … et
  `Δ(P)` le sous-ensemble des racines simples."
- **I.1, printed p. 240.** "On définit un homomorphisme `H_G : G → a_G` par la relation
  `q^{−⟨χ,H_G(g)⟩} = |χ|_F(g)` pour tout `χ ∈ Rat(G)`." "Les définitions ci-dessus s'appliquent
  à tout sous-groupe de Lévi `M`, en remplaçant `G` par `M`. On pose plus simplement
  `H_0 = H_{M_0}`. On définit `M̄_0^+ = H_{M_0}^{−1}(ā_0^+)`." Also: "`δ_H` est le module du
  groupe `H`", with `∫_G f(g) dg = ∫_{U×M×K} f(umk) δ_P(m)^{−1} dk dm du`.
- **Proposition I.4.3, printed p. 245.** "Pour `m ∈ M̄_0^+` et `t ∈ ℝ`, définissons un
  sous-groupe parabolique standard `P_{m,t} = M_{m,t}U_{m,t}` par l'égalité
  `Δ_0^{M_{m,t}} = {α ∈ Δ_0 ; ⟨α, H_0(m)⟩ ⩽ t}`. Proposition I.4.3. Soit `(v, v̌) ∈ V × V̌`. Il
  existe `t > 0` tel que pour tout `m ∈ M̄_0^+`, on ait l'égalité
  `δ_P(m)^{−1/2}⟨π(m)v, v̌⟩ = ⟨π_P(m)j_P(v), ǰ_{P̄}(v̌)⟩_P`, où `P = P_{m,t}`."
- **I.5, printed pp. 245–246.** B-families of admissible representations: "les résultats des
  parties I.3 et I.4, à l'exception de I.4.4, restent valables pour les `B`-familles
  algébriques de représentations admissibles." This is the source of uniformity over the orbit.
- **III.5, printed p. 269.** "Pour une fonction `f : A_M → ℂ`, on écrit
  `lim_{a →_P ∞} f(a) = 0` si pour tous `ε, η > 0`, il existe `R > 0` tel que, pour tout
  `a ∈ A_M` vérifiant les conditions (i) `⟨α, H_M(a)⟩ > R` pour tout `α ∈ Σ(P)`;
  (ii) `⟨α, H_M(a)⟩ > η⟨β, H_M(a)⟩` pour tous `α, β ∈ Σ(P)`, on ait `|f(a)| < ε`."
- **Lemma III.5.1, printed pp. 269–270.** "Soit `f ∈ A^w(G)`. Il existe un unique élément
  `f^w_P ∈ A^w(M)` tel que pour tout `m ∈ M`,
  `lim_{a →_P ∞} [δ_P(ma)^{−1/2} f(ma) − f^w_P(ma)] = 0`." In the proof (p. 270),
  `f^w_P(m) = ⟨π^w_P(m) j^w_P(v), ǰ^w_{P̄}(v̌)⟩_P`, the coefficient of the component `V^w_P` of
  the Jacquet module on which `A_M` acts with exponents of real part `0`.
- **Lemma VI.2.1 (ii), printed p. 296, and its proof, pp. 297–298.** "(ii) Pour tout
  sous-groupe parabolique semi-standard `P′ = M′U′` de `G` et tout `m′ ∈ M′`, les applications
  `ω ↦ (E^G_P ψ_ω)_{P′}(m′)` et `ω ↦ (E^G_P ψ_ω)^w_{P′}(m′)` sont `C^∞` sur `O`." The proof
  splits the exponents `E = E^w ∪ E^+` according to `Re[(wμ)|_{A_{M′}}] = 0`, resp. `≠ 0`,
  fixes `a ∈ A_{M′}` with `|α(a)|_F < 1` for `α ∈ Σ(P′)`, and shows `|(sp_χ ν)(a)| = 1` for
  `ν ∈ E^w` and, "d'après la Proposition III.2.2", `|(sp_χ ν′)(a)| < 1` for `ν′ ∈ E^+`.
- **Definitions before Lemma VI.2.3 and the lemma, printed p. 299.** "Si `P′ = M′U′` est un
  sous-groupe parabolique standard de `G` et `δ` un réel `> 0`, on pose
  `D_{M′}(δ) = {m ∈ M̄_0^+ ; ∀α ∈ Δ_0 − Δ_0^{M′}, ⟨α, H_0(m)⟩ ⩾ δ|H_0(m)|}`. Pour tout
  `f ∈ A^w(G)`, on pose `f^+_{P′} = f_{P′} − f^w_{P′}`. Lemme VI.2.3. Soient `P′ = M′U′` un
  sous-groupe parabolique standard de `G`, `δ` un réel `> 0` et `ψ ∈ C^∞(O, P)`. Alors il
  existe `ε > 0` et `C > 0` tels que, pour tous `ω ∈ O` et `m ∈ D_{M′}(δ)`, on ait l'inégalité
  `|(E^G_P ψ_ω)^+_{P′}(m)| ⩽ C Ξ^{M′}(m) e^{−ε|H_0(m)|}`."
- **Proof of VI.2.3, printed pp. 299–301.** "On suppose `P′` propre sinon
  `(E^G_P ψ_ω)^+_{P′} = 0`." Step (1): "D'après I.5 et la Proposition I.4.3, il existe `t > 0`
  tel que, si `m` vérifie les conditions ci-dessus [`m ∈ M̄_0^+`, `⟨α, H_0(m)⟩ ⩾ t` pour tout
  `α ∈ Δ_0 − Δ_0^{M′}`], on ait l'égalité `(E^G_P ψ)_{P′}(m) = δ_{P′}(m)^{−1/2}(E^G_P ψ)(m)`";
  then Lemma VI.2.2, Lemma II.1.1 (`Ξ(m) ⩽ C_3 δ_0(m)^{1/2}(1 + σ(m))^d`,
  `C_4 δ_0^{M′}(m)^{1/2} ⩽ Ξ^{M′}(m)`), and, p. 300, the proof of VI.2.1:
  `(E^G_P sp_χ ψ)^w_{P′}(m′) = Σ_{i=0}^n b_i(χ)(E^G_P sp_χ ψ)_{P′}(a^i m′)` with `b_i` rational
  and regular on `Im X(M)`. Step (2), p. 300: the recursion with
  `r_χ(X) = Π_{ν ∈ E^+}(X − sp_χ ν(a))^{n(ν)}`, which annihilates `(E^G_P sp_χ ψ)^+_{P′}` under
  right translation by `a`. Step (3), p. 301: the compact part `{m ∈ D_{M′}(δ) ; |H_0(m)| ⩽
  tδ^{−1}}` and the shift `m a^{−n}`.
- **Proof of VI.3.1, printed p. 303.** "D'après I.5 et la Proposition I.4.3, il existe `t > 0`
  tel que pour tout `m ∈ M̄_0^+(J)` vérifiant `s(m) ⩾ t`, et pour tout `χ ∈ Im X(M)`, on ait
  les égalités `(E^G_P sp_χ ψ)(m) = δ_{P′}(m)^{1/2}(E^G_P sp_χ ψ)_{P′}(m) =
  δ_{P′}(m)^{1/2}[(E^G_P sp_χ ψ)^w_{P′}(m) + (E^G_P sp_χ ψ)^+_{P′}(m)]`."
- **Proof of VI.3.1, printed p. 305.** "Il existe `δ > 0` tel que `M̄_0^+(J) ⊂ A_G D_{M′}(δ)`
  … En utilisant le Lemme VI.2.3 et les relations (4) et (6) ci-dessus, on voit qu'il existe
  `ε > 0`, `r″ ∈ ℝ` et `D ∈ 𝒟_M` tels que …" The positive part is bounded there by VI.2.3.

## Setting

The orbit section uses the section variables of the published
`RationalInducedOrbitWavePacket`: a maximal split torus `i : S → G` (`hi`), a generic
cocharacter `ν` (`hν`), connected reductive `G` (`hG`), a standard index
`I : Finset (RationalPointFamily.SimpleRoot i ν)` with Levi `M = M_I`, an open subgroup `K`
with `hKc : IsCompact K` and the Iwasawa pair `hPK` for `P_∅(F)`, an irreducible admissible
`π` of `M_I(F)` (carrier universe `uV`), a central subgroup `C` with quotient Haar measure `mu`
and **square integrability `hsq` as the only representation premise**. The orbit `O` is the
published `discreteSeriesOrbit` and `ψ` ranges over `rationalInducedSmoothOrbitSections`
(the source's `C^∞(O, P)`); `f_ω` is `rationalInducedOrbitCoefficientMap … ψ ω` (read as the
function `g ↦ f_ω(g)`). The second parabolic `P′ = M′U′` is the actual standard parabolic of a
second standard index `I′`, so `Δ_0^{M′} = rootSet i ν I′`; every `I′` is allowed, including
`I′ = all simple roots` (`P′ = G`). `A` with `qA : A → S` and
`hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I′) A qA` is an actual compatible
split component of `M′`, and `standardComponentHom hA : A(F) →* M′(F)`.

## Classification of the content

### Imported proofs (published theorems used)

- `iSupIndep_jointGenEigenspace` (`ExponentDirectSum`): independence of joint generalized
  eigenspaces, giving the disjointness of the weak and positive exponent spaces.
- `exists_sum_mem_jointGenEigenspace` (`ExponentDecomposition`): decomposition of a vector of
  a finite-dimensional stable subspace into joint generalized eigenvectors (used for right-finite
  functions).
- `aeval_rightFunctions_coefficient` (`ExponentDecomposition`).
- `HasStandardConstantTerm.isRightFinite` (`StandardCasselmanConstantTerm`).
- `standardLevi_empty_eq_torusCentralizer_of_generic` (`MinimalStandardDynamicComparison`),
  `torusCentralizer_carrier_base`, `centralizerPoints_le_standardLeviPoints`.
- `restrictionEvaluation_bijective_of_torusCentralizer`
  (`BruhatTits.Cartan.CentralizerValuationComparisonProof`), `centralizerValuation_spec`,
  `rationalNormLogarithm_eq_intValuation`, `rationalNormLogarithm_spec`.
- `positiveRelativeRoots_induction`, `simpleRelativeRoots_subset_positive`.
- `modularCharacter_standardParabolicPoints` (`RationalTemperedInduction`) and
  `locallyCompactSpace_standardParabolicPoints_rootSet` (`RationalInducedCoefficients`).

### Imported constructions (published definitions reused, not rebuilt)

`rationalInducedOrbitCoefficientMap`, `rationalInducedSmoothOrbitSections`,
`discreteSeriesOrbit` (orbit coefficients); `standardConstantTerm`, `HasStandardConstantTerm`,
`standardHalfModulus`, `standardRadicalModulus`, `standardComponentHom` (Proposition I.6.2);
`BruhatTits.Cartan.centralizerValuation`, `BruhatTits.Cartan.dominantCentralizer`,
`BruhatTits.Cartan.restrictionEvaluation` (centralizer valuation); `rationalLeviXi`
(`Ξ^{M′}`); `jointGenEigenspace`, `IsRightFinite`, `GroupAction.rightFunctions`;
`TendstoZeroAlongParabolic` (III.5); `RealTorusSpace.V`, `RealTorusSpace.eval`;
`map_mem_standardLeviPoints_empty`; the structural predicates `IsStandardCocharacter`,
`CompactOpenNormalBasis`, `StandardParabolicBasisMember`, `SimultaneousStandardBasisAt`,
`RationalPointFamily.FiniteCartanCovering`, `StandardLeviCartanCovering`.

### New definitions

| Lean | Meaning |
| --- | --- |
| `componentRightTranslation j` | `a ↦ (φ ↦ (m ↦ φ(m j(a))))`, right translation by `j(A)` on `M → ℂ` |
| `unitaryExponents A` | `{χ : A → ℂ ; ∀ a, ‖χ a‖ = 1}` (the source's `Re(χ) = 0`) |
| `weakExponentSpace j`, `positiveExponentSpace j` | `⨆` of `jointGenEigenspace` over unitary, resp. non-unitary `χ` |
| `weakPart j φ`, `positivePart j φ` | the weak component of `φ` (total; `0` if no split), and `φ − weakPart j φ` |
| `minimalLeviInclusion hG hi hν J` | `M_0(F) = M_∅(F) →* M_J(F)`, `m ↦ m` |
| `rationalMinimalH0 hG hi hν` | Waldspurger's `H_0 : M_0(F) → V(S) = ℝ ⊗ X_*(S)` |
| `rationalMinimalClosedChamber` | `M̄_0^+` |
| `rationalConstantTermThresholdRegion J t` | `{m ∈ M̄_0^+ ; ⟨α, H_0(m)⟩ ≥ t, α ∈ Δ_0 − J}` |
| `rationalPositivePartRegion N J δ` | `D_{M′}(δ)` for the norm `N` and `J = Δ_0^{M′}` |
| `HasRationalPositivePartDecay N J Φ B` | the VI.2.3 conclusion for a family `Φ` and weight `B` |
| `rationalOrbitConstantTerm … ψ ω` | `(f_ω)_{P′}` |
| `rationalOrbitWeakConstantTerm … ψ ω` | `(f_ω)^w_{P′}` |
| `rationalOrbitPositiveConstantTerm … ψ ω` | `(f_ω)^+_{P′}` |
| `rationalComponentH0` | `a ↦ H_0(a)` on `A(F)` (via `A → S → M_0`) |
| `rationalOutsideSimpleForms J` | `Δ_0 − J` as a `Finset` of linear forms on `V(S)` |

### New proved lemmas

`componentRightTranslation_apply`, `disjoint_weakExponentSpace_positiveExponentSpace`,
`weakPart_add_positivePart`, `weakPart_eq_of_mem` (uniqueness),
`weakPart_mem_and_positivePart_mem`, `sum_filter_mem_weakExponentSpace`,
`sum_filter_not_mem_positiveExponentSpace`, `weakPart_sum`, `positivePart_sum`,
`coefficient_mem_jointGenEigenspace`, `weakPart_coefficient`, `mem_sup_of_isRightFinite`;
`standardLeviPoints_empty_eq_centralizerPoints`, `standardLeviPoints_empty_le`,
`coe_minimalLeviInclusion`, `minimalLevi_restrictionEvaluation_bijective`,
`rationalMinimalH0_mul`, `rationalMinimalH0_spec`,
`mem_rationalMinimalClosedChamber_iff_dominantCentralizer`,
`rationalPositivePartRegion_subset_of_le`, `HasRationalPositivePartDecay.of_equivalent`,
`rationalOrbitWeakConstantTerm_add_positive`, `rationalOrbitWeakConstantTerm_mem`,
`modularCharacter_standardParabolicPoints_leviPoint`.

### New targets (Prop-valued `def`s, not proved)

`RationalOrbitConstantTermExistenceStatement`, `RationalOrbitConstantTermThresholdStatement`,
`RationalOrbitWeakConstantTermLimitStatement`, `RationalOrbitPositiveConstantTermDecayStatement`
(principal target). Each takes the orbit data, `I′`, `A`, `qA`, `hA` as parameters (the decay
target also the Levi Iwasawa pair `hM′` needed by `rationalLeviXi`).
The weak-limit and decay propositions additionally quantify explicitly over
`[BorelSpace (M_I(F) ⧸ C)]` inside their Prop bodies, for the already supplied
quotient measurable-space instance.

### Unresolved obligations

The four targets are proved in separate modules: `rationalOrbitConstantTermExistence`
(`RationalOrbitConstantTermExistenceProof`), `rationalOrbitConstantTermThreshold`
(`RationalOrbitConstantTermThresholdProof`), `rationalOrbitWeakConstantTermLimit`
(`RationalOrbitWeakConstantTermLimitProof`) and `rationalOrbitPositiveConstantTermDecay`
(`RationalOrbitPositiveConstantTermDecayProof`). This module does not prove them, nor the inputs
listed under "Realization inputs" or the comparison identities listed under "Moduli" and
"`Δ(P′)` and `Σ(P′)`".

## Definitions in detail

### Weak and positive parts (generic)

For a group `M`, a commutative group `A` and `j : A →* M`, `weakExponentSpace j` and
`positiveExponentSpace j` are the spans of the joint generalized eigenspaces
`{φ ; ∀ a, ∃ k, (ρ(j a) − χ(a))^k φ = 0}` of the right translations `ρ(j a)` on all functions
`M → ℂ`, over the unitary exponents `‖χ(a)‖ = 1 ∀ a`, resp. the others. They are independent
(`disjoint_weakExponentSpace_positiveExponentSpace`). `weakPart j φ` is the unique `w` in the
weak space with `φ − w` in the positive space, chosen with `Classical.choice` when it exists,
and `0` otherwise; so the definition is **total** and presupposes neither `f ∈ A^w(G)` nor
right finiteness. `positivePart j φ = φ − weakPart j φ`, so `weakPart + positivePart = φ`
always (`weakPart_add_positivePart`).

When `φ` has a finite expansion `φ = Σ_χ φ_χ` into joint generalized eigenfunctions,
`weakPart j φ = Σ_{χ unitary} φ_χ` and `positivePart j φ = Σ_{χ not unitary} φ_χ`
(`weakPart_sum`, `positivePart_sum`): the weak part is "the sum of the components of the finite
expansion whose exponents are unitary". Every `IsRightFinite j.range φ` function has such an
expansion (`mem_sup_of_isRightFinite`, through `exists_sum_mem_jointGenEigenspace`).

For a coefficient `m ↦ lam (J(m) y)` and `y = Σ_χ y_χ` with `y_χ` joint generalized
eigenvectors of `J ∘ j` (as produced by `exists_sum_mem_jointGenEigenspace`),
`weakPart_coefficient` gives `weakPart j (m ↦ lam (J(m) y)) = m ↦ lam (J(m) Σ_{χ unitary} y_χ)`.
This is the function `F^w` constructed inside the proof of `exists_weak_positive_decomposition`
(`ExponentDecomposition`), and it is the source's
`f^w_P(m) = ⟨π^w_P(m) j^w_P(v), ǰ^w_{P̄}(v̌)⟩_P` of the proof of III.5.1 (p. 270), where
`V^w_P` is the sum of the generalized eigenspaces of `A_M` with exponents of real part `0`.

The source's exponents are characters of `A_M`; `Re(χ) = Re(|χ|) = 0` iff `|χ| = 1` (I.1,
p. 239). Our exponents are functions `χ : A → ℂ`; a joint generalized eigenspace containing a
nonzero function forces `χ` to be multiplicative with `χ(1) = 1`
(`map_mul_of_mem_jointGenEigenspace`, `map_one_of_mem_jointGenEigenspace`), so the unitary
condition is the source's.

### The actual constant terms

`rationalOrbitConstantTerm … ψ ω := standardConstantTerm hA (fun g => f_ω g)`, the published
Proposition I.6.2 constant term on `M′(F)` for the compatible split component `A`, normalized by
`δ_{U′}` (see "Moduli"). `rationalOrbitWeakConstantTerm` and `rationalOrbitPositiveConstantTerm`
are `weakPart`/`positivePart` of it along `standardComponentHom hA : A(F) →* M′(F)`, i.e. along
the actual split component `A_{M′}(F)`. Their sum is `(f_ω)_{P′}`
(`rationalOrbitWeakConstantTerm_add_positive`, the source's `f^+_{P′} = f_{P′} − f^w_{P′}` of
p. 299). When `HasStandardConstantTerm hA f_ω` holds, the published constant term is right
finite for `A(F)`, so the two parts are its unitary and non-unitary components
(`rationalOrbitWeakConstantTerm_mem`). That the weak part defined this way is the source's
`f^w_{P′}` of Lemma III.5.1 is the content of the target
`RationalOrbitWeakConstantTermLimitStatement` together with the published uniqueness
`eq_of_tendstoZeroAlongParabolic` (`WeakConstantTermUniqueness`) and
`existsUnique_tendstoZeroAlongParabolic_sub` (`WeakConstantTermExistence`).

### `M_0(F)`, `H_0`, `M̄_0^+`

The actual minimal Levi is `M_0(F) := standardLeviPoints i ν ∅`, the points of the minimal
standard Levi scheme `M_∅`; `standardLeviPoints_empty_eq_centralizerPoints` proves
`M_∅(F) = Z_G(S)(F) = centralizerPoints i` for generic `ν`. These are **all** points of
`M_0(F)`, not torus points, lattice points or a uniformizer-power section.

`rationalMinimalH0 hG hi hν m` is the published `centralizerValuation` of `M_∅` (with the
inclusion `S → M_∅` given by `Standard.leviTorusHom i ν ∅`), whose bijectivity hypothesis is
`minimalLevi_restrictionEvaluation_bijective` (the published comparison
`restrictionEvaluation_bijective_of_torusCentralizer`, since `M_∅` represents `Z_G(S)`), read
through `Standard.leviPointsEquiv i ν ∅`. It is additive (`rationalMinimalH0_mul`) and
satisfies **the I.1 convention** (`rationalMinimalH0_spec`):
`q^{−⟨χ|_S, H_0(m)⟩} = |χ(m)|_F` for every rational character `χ` of `M_∅`, `q` the residue
cardinality, `|·|_F` the residue-normalized absolute value, and `⟨χ|_S, ·⟩` the evaluation of
the restriction `χ|_S ∈ X^*(S)` on `V(S)`. Here `a_0 = Hom(Rat(M_0), ℝ)` of the source is
identified with `V(S) = ℝ ⊗ X_*(S)` by restriction of characters to `S` (bijective after
`⊗ ℝ` by the comparison just cited), which is the source's identification
`Rat(M_0) ⊗ ℚ ≃ Rat(A_0) ⊗ ℚ`.

`rationalMinimalClosedChamber` is `{m ; ∀ α ∈ Δ_0, 0 ≤ ⟨α, H_0(m)⟩}` with
`Δ_0 = simpleRelativeRoots i ν`, i.e. `M̄_0^+ = H_0^{−1}(ā_0^+)`.
`mem_rationalMinimalClosedChamber_iff_dominantCentralizer` proves it equals (through
`leviPointsEquiv`) the published `dominantCentralizer` of `M_∅`, whose inequalities are over
all positive relative roots, by `positiveRelativeRoots_induction`. The published
`rationalMinimalChamber` (`RationalMinimalChamber`) is the image of the torus points
`S(F)` only and is not used here.

### The regions and the norm

`rationalConstantTermThresholdRegion J t` and `rationalPositivePartRegion N J δ` are the closed
subsets of `M_0(F)` displayed in the table, with `J = Δ_0^{M′} = rootSet i ν I′`. In
`D_{M′}(δ)` the source's `|·|` is an arbitrary `Seminorm ℝ (RealTorusSpace.V S)` `N`; the
decay target quantifies over **every** such `N` with `N v = 0 → v = 0` (every norm on the
finite-dimensional space `V(S)`; `IsSplitTorus.finite_realCocharacterSpace`). The choice does
not matter: all norms on a finite-dimensional real space are equivalent, and
`HasRationalPositivePartDecay.of_equivalent` proves that if `N₁ ≤ c₁N₂` and `N₂ ≤ c₂N₁`
(`c₁, c₂ > 0`) and `B ≥ 0`, decay for `N₁` (for all `δ > 0`) implies decay for `N₂` (for all
`δ > 0`), through `D^{N₂}_{M′}(δ) ⊆ D^{N₁}_{M′}(δ/c₁)` (`rationalPositivePartRegion_subset_of_le`)
and `e^{−ε N₁/…}` comparison. So the target for all norms is equivalent to the target for one
norm (the equivalence of norms itself is Mathlib's, used only in this explanation).

### `Ξ^{M′}`

The decay bound uses the published `rationalLeviXi hKc hM′` for the index `I′`, evaluated at
`minimalLeviInclusion … m ∈ M′(F)`; `hM′` is the Iwasawa pair of `P_∅(F) ∩ M′(F)` and
`K ∩ M′(F)` required by `rationalLeviXi`.

## Quotient-measure compatibility

The weak-limit and positive-decay targets require the supplied measurable
structure on `M_I(F) ⧸ C` to be the Borel sigma algebra of its quotient topology.
Each proposition binds `[BorelSpace (M_I(F) ⧸ C)]` explicitly inside its Prop
body. An unused section instance would not impose this condition on the target.
`Measure.IsHaarMeasure` on an independently chosen measurable space does not
itself identify that measurable space with the Borel structure.

With it, the square-integrability premise is read as an analytic condition
for the topological quotient. Lemma III.5.1 starts with a
tempered coefficient `f ∈ A^w(G)`, and VI.2.3 uses the unitary/non-unitary exponent
split of those coefficients; neither source passage asserts their conclusions
for square integrability on an unrelated sigma algebra. Borel compatibility is
a natural sufficient requirement for the intended Haar-measure interface, not
a claim of the weakest possible measure-theoretic condition.

The orbit and constant-term constructions and their algebraic decomposition laws
continue to accept the original measurable data. The existence and uniform
threshold targets use admissibility and the algebraic-family result I.5, so the
Borel requirement is added only to the weak-limit and decay targets.
Their structural premises and conclusions are otherwise the same. In particular,
Borel compatibility supplies neither induced temperedness nor an exponent bound
nor a coefficient estimate. For the general central subgroup `C` in this module,
a proof must still justify the passage from its square-integrability premise to
the actual split-center analytic results used by the source. The downstream
VI.3.1 target in `StandardLeviPlancherelWavePacketSchwartz` already assumes Borel
compatibility for its actual split-center quotient.

## Targets

All four targets share the displayed structural premises, which are exactly those the published
constant-term and Cartan interfaces take: a standard cocharacter `ζ` of `I′`
(`IsStandardCocharacter`), Renard's V.5.2 data `K0`, `B` (`CompactOpenNormalBasis K0 B`) with
the basis-member clauses of `P′` for `qA` (`StandardParabolicBasisMember`), and, for the three
estimate targets, `K0` open and compact, `SimultaneousStandardBasisAt i ν K0` (V.5.2 for all
standard parabolics and their Levi clauses), `RationalPointFamily.FiniteCartanCovering F i ν K0`
and `StandardLeviCartanCovering F i ν J K0` for every `J ⊆ Δ_0` (the Levi clauses of V.5.1 (4)).
**None** of the following is a premise: a coefficient `Ξ` bound for `π` (Corollary III.1.2),
Lemma VI.2.2, the II.1.1 bound, a bound on the exponents of the constant term, existence or
properties of a weak constant term, the threshold, or any decay estimate.

1. **`RationalOrbitConstantTermExistenceStatement`** (Proposition I.6.2 for the orbit
   coefficients). Under `ζ`, `B`, the basis-member clauses (the hypotheses of the published
   `exists_standardConstantTerm`), every `f_ω` satisfies `HasStandardConstantTerm hA f_ω`. It is
   published as a target; it follows from
   `exists_standardConstantTerm` once `f_ω` is exhibited as a coefficient of the admissible
   induced representation `I^G_P(ω)` (`RationalOrbitConstantTermExistenceProof`).
2. **`RationalOrbitConstantTermThresholdStatement`** (I.4.3 with I.5, as used on pp. 299 and
   303). For every `ψ` there is `t > 0` such that for every `ω ∈ O` and every
   `m ∈ M̄_0^+` with `⟨α, H_0(m)⟩ ≥ t` for `α ∈ Δ_0 − Δ_0^{M′}`,
   `f_ω(m) = δ_{U′}(m)^{1/2} (f_ω)_{P′}(m)` (with `standardHalfModulus`, see "Moduli"). This
   is p. 299's `(E^G_P ψ)_{P′}(m) = δ_{P′}(m)^{−1/2}(E^G_P ψ)(m)` and the first equality of
   p. 303; `t` is uniform over the orbit, as I.5 provides. The second equality of p. 303 is
   then `rationalOrbitWeakConstantTerm_add_positive`. (Page 303 states it on
   `M̄_0^+(J) ∩ {s(m) ≥ t}`; the p. 299 form used here implies it, since on that set the
   simple roots outside `Δ_0^{M′} = Δ_0 − J` have value `s(m) ≥ t`.)
3. **`RationalOrbitWeakConstantTermLimitStatement`** (Lemma III.5.1). Assuming the quotient
   Borel compatibility above, for every `ψ`, `ω ∈ O`
   and `m′ ∈ M′(F)`: `TendstoZeroAlongParabolic H S` of
   `a ↦ δ_{U′}(m′a)^{−1/2} f_ω(m′a) − (f_ω)^w_{P′}(m′a)` on `A(F)`, with `H = rationalComponentH0`
   (`H_0` of the image of `a` in `M_0(F)`, which is the source's `H_{M′}(a)` under
   `a_{M′} ⊂ a_0`) and `S = rationalOutsideSimpleForms (Δ_0^{M′})`. Combined with the published
   uniqueness results, it identifies the weak part defined here with the source's `f^w_{P′}`.
4. **`RationalOrbitPositiveConstantTermDecayStatement`** (Lemma VI.2.3, principal target).
   Assuming the same quotient Borel compatibility, for every norm `N` on `V(S)`, every `ψ` and every `δ > 0`, there are `ε > 0` and `C > 0`
   such that for **every** `ω ∈ O` and every `m ∈ D_{M′}(δ)`,
   `‖(f_ω)^+_{P′}(m)‖ ≤ C Ξ^{M′}(m) e^{−ε N(H_0(m))}`. The constants depend on `ψ`, `I′`,
   `δ` and `N` only, uniformly over the orbit, as in the source.

The improper case `I′ = Δ_0` (`P′ = G`) is included; there the source notes
`(E^G_P ψ_ω)^+_{P′} = 0`. That vanishing is not proved here.

## Moduli

The published constant term normalizes by `δ_{U′} = standardRadicalModulus`, the Haar modulus
of conjugation by `M′(F)` on the closed radical `U′(F)`; Waldspurger normalizes by `δ_{P′}`,
"le module du groupe `P′`" (p. 240), with the integration formula
`∫_G f = ∫_{U×M×K} f(umk) δ_P(m)^{−1}`, so that `δ_{P}(m) = |det Ad(m)|_{Lie U}|_F`.

- **Proved here:** `modularCharacter_standardParabolicPoints_leviPoint` — for `m ∈ M′(F)`,
  Mathlib's `Measure.modularCharacter` of the group `P′(F)` at `m` equals `δ_{U′}(m)` (from the
  published `modularCharacter_standardParabolicPoints`).
- **Not proved (in this module or the Library):** that Mathlib's `modularCharacter`
  convention agrees with Waldspurger's "module du groupe", and the identity
  `δ_{U′}(m) = |det Ad(m)|_{Lie U′}|_F`. Granting them, `δ_{U′} = δ_{P′}` on `M′(F)` and the
  targets are literally Waldspurger's. The published `StandardCasselmanConstantTerm.md`
  ("Moduli") records the same gap.

## `Δ(P′)` and `Σ(P′)`; `H_{M′}` and `H_0`

III.5 uses `Σ(P′)`; `RationalOrbitWeakConstantTermLimitStatement` uses the simple roots
`Δ_0 − Δ_0^{M′}`, whose restrictions to `A_{M′}` form `Δ(P′)`, evaluated on `H_0(a)`. The two
limit notions agree (not proved here): `Δ(P′) ⊆ Σ(P′)`, and every `β ∈ Σ(P′)` is a
nonnegative integer combination `Σ n_γ γ` of `Δ(P′)` with some `n_γ ≥ 1` and bounded
coefficients, so condition (i) for `Δ(P′)` with `R` gives (i) for `Σ(P′)` with `R`, and
condition (ii) for `Δ(P′)` with `η` gives (ii) for `Σ(P′)` with `η/c` for a constant `c`
depending only on the root data; conversely (i), (ii) for `Σ(P′)` restrict to `Δ(P′)`. Since
`TendstoZeroAlongParabolic` quantifies over all `ε, η > 0`, the regions are cofinal in each
other and the notions coincide. Similarly, `H_0(a)` for `a ∈ A(F)` is the image of
`H_{M′}(a)` under `a_{M′} ⊂ a_0`, and `⟨α, H_0(a)⟩ = ⟨α|_{A_{M′}}, H_{M′}(a)⟩`.

## Relation to the abstract engines

- **`PositivePartDecay`** (`exists_norm_le_exp_of_aeval_eq_zero`, abstract VI.2.3). Dictionary:
  the group is `M_0(F)` (or `M′(F)` restricted to `M_0(F)` via `minimalLeviInclusion`), `H` is
  `rationalMinimalH0` (additive by `rationalMinimalH0_mul`), `E = V(S)` normed by `N`,
  `S₀ = Δ_0^{M′}` and `S = Δ_0 − Δ_0^{M′}` as linear forms (`rationalOutsideSimpleForms`), the
  family index is `ω ∈ O`, `F_ω = (f_ω)^+_{P′} ∘ minimalLeviInclusion`, `B = Ξ^{M′}`. The
  engine's region `(∀ β ∈ S₀, 0 ≤ β(Hg)) ∧ (∀ α ∈ S, δ‖Hg‖ ≤ α(Hg))` is
  `rationalPositivePartRegion N J δ` (for `δ ≥ 0`), its shifted chamber
  `(∀ β ∈ S₀, 0 ≤ β(Hg)) ∧ (∀ α ∈ S, t ≤ α(Hg))` is `rationalConstantTermThresholdRegion J t`
  (for `t ≥ 0`), and its conclusion is `HasRationalPositivePartDecay`.
- **`WeakPartProjection`** (`exists_norm_le_exp_of_decomposition`, VI.2.1 (ii) translate
  combination). It takes `F = F^w + F^+` with annihilating polynomials of uniform degrees whose
  roots have modulus `1`, resp. `≤ θ < 1`; here `F = (f_ω)_{P′}`, `F^w`, `F^+` the actual weak
  and positive parts, and the bound on `F` on the shifted chamber comes from the threshold
  target plus VI.2.2 and II.1.1.
- **`ExponentDecomposition`** (`exists_weak_positive_decomposition`). Its `F^w`, `F^+` for a
  coefficient are the coefficients of the unitary, resp. other, components; `weakPart_coefficient`
  shows that `weakPart` of a coefficient is exactly that `F^w`. That an element of
  `weakExponentSpace j` (resp. `positiveExponentSpace j`) is annihilated by
  `Π (X − χ(a₀))^{k_χ}` is elementary from the definitions but not stated here.
- **`FiniteFunctionExpansion`**, **`WeakConstantTermUniqueness`**, **`WeakConstantTermExistence`**:
  `IsRightFinite` right-finite functions have the finite expansion used by `weakPart`
  (`mem_sup_of_isRightFinite`); the uniqueness results identify the limit in target 3.

## Realization inputs

To prove the targets (in particular VI.2.3) from the engines, the proofs need:

1. **Lemma VI.2.1 (ii) on actual points**: for the actual `(f_ω)_{P′}`, annihilating
   polynomials of `F^w`, `F^+` under right translation by one `a ∈ A_{M′}(F) ∩ M̄_0^+`, of
   degrees uniform over the orbit, with the root bounds (unitary for `E^w`, uniformly `≤ θ < 1`
   for `E^+`), equivalently the `b_i(χ)` representation of p. 300.
2. **Lemma VI.2.2 without a coefficient premise**: the published
   `exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi` takes `hcoeff`; it must be
   discharged by Corollary III.1.2 (`RationalSquareIntegrableRapidDecayStatement`, proved as
   `rationalSquareIntegrableRapidDecay`) for the square-integrable `π`.
3. **Lemma II.1.1** (the upper bound is `RationalXiUpperBoundStatement`, proved as
   `rationalXiUpperBound`):
   `Ξ(m) ≤ C δ_0(m)^{1/2}(1 + σ(m))^d` and `C δ_0^{M′}(m)^{1/2} ≤ Ξ^{M′}(m)` on `M̄_0^+`.
4. **Exponent bounds of tempered induced representations**: Proposition III.2.2
   (`TemperedExponentCone`), Casselman's square-integrability
   criterion (Renard VII.1.2, for represented parabolics), giving `|(sp_χ ν)(a)| < 1` for `ν ∈ E^+`.
5. The threshold target (2) itself, the existence target (1), and the structural existence of the
   V.5.2 data (`JointSpecialCompactBasisExistenceStatement`).
6. Auxiliary facts for the engine hypotheses: `Ξ^{M′}(m a) = Ξ^{M′}(m)` for `a ∈ A_{M′}(F)`, a
   subadditive height `σ` on `M_0(F)` with `1 + σ ≤ C(1 + |H_0|)`, compactness of
   `{m ∈ D_{M′}(δ) ; |H_0(m)| ≤ tδ^{−1}}` modulo the kernel of `H_0` (p. 301), and the moduli
   identities above.

These are inputs of the eventual proofs, **not** premises of the targets. This module does not
prove Lemma VI.2.3 or Proposition VI.3.1, and does not supply the weak-constant-term expansion
into lower-Levi packets (V.1.1, Corollary V.2.3), which is separate.

## Check

`lean_check` (Library base
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`): 0 errors, 0 warnings. Inspection of each of the
four targets reports `statement_returns_prop: true`, level parameters `u, uV`, axioms
`propext`, `Classical.choice`, `Quot.sound`.

The two propositions with the quotient Borel structure were checked in the same
way: compilation and exact proposition inspection report zero
errors and warnings, `statement_returns_prop: true`, independent level parameters
`u, uV`, and only `propext`, `Classical.choice`, `Quot.sound`.
