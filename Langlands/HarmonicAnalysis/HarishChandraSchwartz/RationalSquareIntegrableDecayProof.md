# Proof of Waldspurger's Corollary III.1.2 on actual rational points

The height bound used in the last step is the helper module `RationalCartanCellHeight`, which is
ported together with this module.

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecayProof`,
namespace `Langlands.HarishChandraSchwartz`.

The final theorem

`rationalSquareIntegrableRapidDecay : RationalSquareIntegrableRapidDecayStatement.{u, uV}`

proves the Library's statement of Corollary III.1.2 at arbitrary universes `u` (field) and `uV`
(representation carriers). It adds no hypothesis: the only structural premises used are the two
premises of the statement itself, `SimultaneousStandardBasisAt i ν K0` and
`FiniteCartanCovering F i ν K0`. Every representation-theoretic input is a published theorem
imported by Lean name. The proofs use no `sorry` and no new axioms. The axioms reported for the
final theorem are `propext`, `Classical.choice` and `Quot.sound`.

The statement, its notation and its correspondence with the source are described in
`RationalSquareIntegrableDecay.md`. Briefly: `Ξ = rationalXi hKc hPK`, `σ = rationalHeight ρ`,
`G¹ = Plancherel.rationalCommonNormKernel G`, `ϖ^y = Aubert.General.uniformizerPowers i (.ofAdd y)`
for a cocharacter `y` of `S`, `⟨β, y⟩ = simpleRootPairing i ν β y` for a simple root `β`,
`P₀(F) = standardParabolicPoints i ν ∅` and `δ₀ = rationalMinimalModulus i ν` (the modulus of
`P₀(F)`).

## Source and route

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`).
Corollaire III.1.2 is on printed p. 263 and its proof on printed p. 264 (PDF p. 30).

Waldspurger's proof: reduce to `f(g) = ⟨π(g)v, v̌⟩` and, "grâce à I.1 (4) et à un argument de
`K`-finitude", to `g ∈ M̄₀⁺ ∩ G¹`; fix a standard parabolic `P = MU` and bound
`a ↦ δ_P(a)^{1/2}⟨π_P(a)v_P, v̌_{P̄}⟩_P` on `Ā₀⁺ ∩ A_M ∩ G¹`. This Jacquet coefficient is
`δ_P^{1/2}` times a finite sum `Σ_χ χ(a) Q_χ(H_M(a))`; Lemma II.1.1 gives
`δ_P(a)^{1/2} ≤ C₁Ξ(a)`, the polynomials satisfy `|Q_χ(H_M(a))| ≤ C₂(1 + σ(a))^d`, and
Casselman's criterion (Proposition III.1.1, `Re(χ) ∈ ⁺a_P^{G*}`) gives
`|χ(a)| ≤ C₃q^{−εσ(a)}`.

The Lean proof follows the same plan but uses different intermediate results:

- **Exponents.** Casselman's criterion enters through its published necessity half
  `RepresentedParabolic.arbitraryParabolicCasselmanNecessity` (for square integrability modulo the
  full center) and the published passage
  `RepresentedParabolic.strictStandardExponents_of_positiveRepresented` to the strict
  normalized Jacquet exponent condition `HasStrictNormalizedJacquetExponents` along the standard
  parabolics `P_J`.
- **Jacquet coefficients.** Instead of the finite-function expansion with polynomial factors, the
  proof uses the published `rationalCompactTranslateCoefficientBound`. From strict exponents it
  gives geometric bounds `C ∏ r_a^{n_a}` with `r_a² < δ₀(ϖ^{x_a})` along a finite family of rays
  `x_a`, uniformly on compact translates. No polynomial factor and no `K`-finiteness argument
  is needed.
- **Reduction to the chamber.** The covering premise `FiniteCartanCovering` puts every point in a
  Cartan cell `K0 ϖ^y f K0` with `y` dominant (`exists_mem_rationalCartanCell`). The published
  `finiteChamberLattice` writes `y = r + Σ_a n_a gen_a + z`, with `r` in a finite set, one
  generator `gen_a` per simple root and `z` orthogonal to all simple roots. The central factor
  `ϖ^z` is removed using the unitary central character. The bounded factor `ϖ^r f` is absorbed
  into the compact translates.
- **Lemma II.1.1** (lower bound) is the published
  `exists_sqrt_rationalMinimalModulus_le_rationalXi`. **Lemma II.1.2** on compact translates is
  proved here (`exists_le_mul_of_compact_translates`) from the published uniform translation
  bound for `Ξ`.
- **From the lattice to `σ`.** The decay is first obtained as `q^{Σ_a n_a}` with `0 < q < 1`.
  It is converted into decay in `σ` by
  `exists_rationalHeight_le_of_mem_rationalCartanCell` (module `RationalCartanCellHeight`). This
  is the upper half of Waldspurger's I.1 (6) on the points of `G¹` in a Cartan cell:
  `σ(g) ≤ C(1 + T)` when the simple-root pairings of `y` are bounded by `T`.

## Section `AbstractDecay` (general lemmas)

- `isRapidlyDecreasingOn_of_geometric`: let `X` be a group, `Ξ, σ ≥ 0`, `N` a subgroup and
  `0 < q < 1`. If every `g ∈ N` has some `m ∈ ℕ` with `‖f(g)‖ ≤ C Ξ(g) q^m` and
  `1 + σ(g) ≤ c(1 + m)`, then `IsRapidlyDecreasingOn Ξ σ N f`. Proof: the published
  `exists_rpow_bound_of_exp_bound` (module `CoefficientRapidDecay`) with one piece, `H(g) = m`
  and rate `−log q > 0`, since `exp(log q · m) = q^m`.
- `exists_le_mul_of_compact_translates` (Lemma II.1.2 on compact translates, with `d = 0`): let
  `X` be a topological group, `K` an open subgroup, `K0` a compact subgroup, `F₁` a finite set
  and `Ξ ≥ 0` bi-`K`-invariant with `UniformTranslationBound Ξ`. Then there is `M` with
  `Ξ(w) ≤ M Ξ(k₁ w t k₂)` for all `w`, all `k₁, k₂ ∈ K0` and all `t ∈ F₁`. Proof: `K0` is covered
  by finitely many cosets `c K` (`exists_finset_mul_mem_of_isCompact`). Write
  `w = c₁⁻¹ (κ₁ (k₁ w t k₂) κ₂) (c₂ t⁻¹)` with `κ₁, κ₂ ∈ K`. Apply the translation bound for the
  finitely many pairs `(c₁⁻¹, c₂ t⁻¹)` and the bi-`K`-invariance. `M` is the maximum of the finitely
  many constants.
- `exists_lt_one_forall_le`: finitely many reals `< 1` are bounded by one `q` with `0 < q < 1`.

## Section `Exponents` (canonical topology `pointTopology`)

- `compactSpace_center_quotient_splitComponent hG hs`: for a split component `s`, the quotient
  of the center of `G(F)` by `A_G(F) = (rationalPoints.map s).range` is compact. Proof: the
  published `centerSplitComponentCompactness` gives compactness of the quotient of the points of
  the scheme-theoretic center. The published `rationalCenterComparison` identifies those points
  with the center of `G(F)`. So the induced continuous map from that compact quotient to the
  quotient of the center of `G(F)` by `A_G(F)` is surjective, and the latter is compact.
- `uniformizerPowers_mem_standardParabolicPoints`: `ϖ^y ∈ P₀(F)`, since it lies in the minimal
  standard Levi `M₀(F)`.
- `hasStrictNormalizedJacquetExponents_universeLift`: if `A` is square integrable modulo
  `A_G(F)` (for any Haar measure on `G(F)/A_G(F)`), then the universe lift
  `SmoothRep.universeLift.{u+1} A` has strict normalized Jacquet exponents along every standard
  parabolic `P_J`. Proof:
  1. `A_G(F)` is closed (`RepresentedParabolic.isClosed_pointImage`) and the center modulo
     `A_G(F)` is compact (previous item). So the published
     `Plancherel.centralSubgroupCoefficientLpComparison` turns square integrability modulo
     `A_G(F)` into square integrability modulo the full center (for a Haar measure on
     `G(F)/Z(G(F))`).
  2. `RepresentedParabolic.arbitraryParabolicCasselmanNecessity` puts the real parts of all
     normalized Jacquet exponents along all represented parabolics in the positive cones.
  3. The standard Casselman presentations of the `P_J`
     (`RepresentedParabolic.standardCasselmanPresentationOfGeometry`, from the published
     standard-representative geometry) and `strictStandardExponents_of_positiveRepresented` (with
     `hasSelectedRootValuationLaw`) give strict exponents for `A`.
  4. `isCentralExponent_normalizedJacquet_equiv_iff`, applied to the equivalence
     `SmoothRep.universeLiftEquiv`, transfers the exponents to the universe lift.
- `exists_coefficient_bound_of_squareIntegrable`: for `A` square integrable modulo `A_G(F)`,
  `K0` with `SimultaneousStandardBasisAt i ν K0`, a finite family of rays `x_a` (for `a ∈ I`) with
  `⟨β, x_a⟩ = 0` for `β ∈ J_a`, `⟨β, x_a⟩ > 0` for `β ∉ J_a` and `J_a` proper, compact sets
  `S₁, S₂`, a finite set `F₀`, a smooth functional `φ` and a vector `v`: there are rates
  `r_a > 0` with `r_a² < δ₀(ϖ^{x_a})` and `C > 0` such that
  `‖φ(π(k₁ ϖ^{Σ_a n_a x_a} t k₂) v)‖ ≤ C ∏_a r_a^{n_a}` for all `n`, all `k₁ ∈ S₁`, `t ∈ F₀`,
  `k₂ ∈ S₂`. Proof: the published `rationalCompactTranslateCoefficientBound` applied to the
  universe lift. The lift is admissible (`SmoothRep.isAdmissible_universeLift_iff`) and has strict
  exponents (previous item). The functional and the vector are transported along
  `universeLiftEquiv`, which does not change the coefficient. That bound gives
  `r_a² Δ_{U_{J_a}}(z_a)⁻¹ < 1` at the central point `z_a = ϖ^{x_a}` of `M_{J_a}(F)`. The
  published `rationalMinimalModulus_eq_standardUnipotentModulus_of_commute` identifies
  `Δ_{U_{J_a}}(z_a)` with `δ₀(ϖ^{x_a})`, since `ϖ^{x_a} ∈ P₀(F) ∩ M_{J_a}(F)` commutes with
  `M_{J_a}(F)`.

The declarations of this section use the canonical topology `pointTopology`, which is the
topology of the published inputs on exponents. The next section uses the local instances of
`RationalWeights`, the setting of the target. The two are linked only through explicit arguments
that agree by unfolding definitions.

## Section `Rational` (the setting of the target)

- `rationalXi_mul_of_mem_center`: `Ξ(a g) = Ξ(g)` for `a ∈ P₀(F)` central in `G(F)`. Proof: the
  published `xi_mul_left_of_eq_one`, since `δ₀(a) = 1`
  (`rationalMinimalModulus_eq_one_of_mem_center`) and `a` commutes with `K`.
- `exists_geometric_coefficient_bound`: for `K0` compact with
  `SimultaneousStandardBasisAt i ν K0`, generators `gen_a` (one for each simple root `a`) with
  `⟨a, gen_a⟩ > 0` and `⟨b, gen_a⟩ = 0` for `b ≠ a`, a finite set `F₁`, `A` square integrable
  modulo `A_G(F)`, `φ` and `v`: there are `0 < q < 1` and `C` with

  `‖φ(π(k₁ ϖ^{Σ n_a gen_a} t k₂) v)‖ ≤ C Ξ(k₁ ϖ^{Σ n_a gen_a} t k₂) q^{Σ n_a}`

  for all `n`, all `k₁, k₂ ∈ K0` and all `t ∈ F₁`. Proof: apply
  `exists_coefficient_bound_of_squareIntegrable` with `J_a` the set of simple roots other than
  `a`. This gives `‖φ(…)‖ ≤ C_c ∏ r_a^{n_a}` with `r_a < s_a = δ₀(ϖ^{gen_a})^{1/2}`. Choose
  `q < 1` with `r_a ≤ q s_a` for all `a`. Then
  `∏ r_a^{n_a} ≤ q^{Σ n_a} ∏ s_a^{n_a} = q^{Σ n_a} δ₀(w)^{1/2}` for `w = ϖ^{Σ n_a gen_a}`,
  because `y ↦ δ₀(ϖ^y)^{1/2}` is a homomorphism. The point `w` lies in `P₀(F)` and in the weak
  chamber of `SimultaneousStandardBasisAt` for `J = ∅` (`uniformizerPowers_mem_standardComponentChambers`,
  as all its simple-root pairings are `≥ 0`). So Lemma II.1.1,
  `exists_sqrt_rationalMinimalModulus_le_rationalXi` applied to a basis member contained in
  `K`, gives `δ₀(w)^{1/2} ≤ C_L Ξ(w)`. Finally `exists_le_mul_of_compact_translates` (with the
  published `rationalXi_mul_mul` and `rationalXi_uniformTranslationBound`) gives
  `Ξ(w) ≤ M Ξ(k₁ w t k₂)`.
- `hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable`: Corollary III.1.2 for one group,
  under the premises of the statement. Proof:
  1. The simple roots form a finite set. For every set `I` of simple roots the published
     `standardCocharacter` gives `ζ` with `⟨β, ζ⟩ = 0` on `I` and `> 0` off `I`. So
     `finiteChamberLattice` gives generators `gen_a` as above and, for the bound `0`, a finite set
     `R` such that every `y` with all `⟨β, y⟩ ≥ 0` is `r + Σ_a n_a gen_a + z` with `r ∈ R`,
     `n_a ∈ ℕ` and `⟨β, z⟩ = 0` for all `β`. For such `z`, `ϖ^z` is central in `G(F)`
     (`commute_uniformizerPowers` and `levi_univ_eq_top`).
  2. Let `F₀` be the finite set of the covering premise and `F₁ = {ϖ^r f : r ∈ R, f ∈ F₀}`
     (finite). `exists_geometric_coefficient_bound` for `F₁` gives `q` and `C`.
     `exists_rationalHeight_le_of_mem_rationalCartanCell` gives `C_σ` with `σ(g) ≤ C_σ(1 + T)`
     for `g ∈ G¹` in the cell of `y` whenever `0 ≤ T` bounds all `|⟨β, y⟩|`.
  3. Let `g ∈ G¹`. By `exists_mem_rationalCartanCell`, `g = k₁ ϖ^y f k₂` with `y` dominant,
     `k₁, k₂ ∈ K0` and `f ∈ F₀`. Decompose `y` as in step 1. Then
     `g = ϖ^z g'` with `g' = k₁ ϖ^{Σ n_a gen_a} (ϖ^r f) k₂`, since `ϖ^z` is central.
  4. The coefficient: `π(ϖ^z)` acts by the unitary central character
     (part of `IsSquareIntegrableModCentralSubgroup`), so `‖φ(π(g) v)‖ = ‖φ(π(g') v)‖`. Also
     `Ξ(g) = Ξ(g')` by `rationalXi_mul_of_mem_center`. So step 2 gives
     `‖φ(π(g) v)‖ ≤ C Ξ(g) q^m` with `m = Σ_a n_a`.
  5. The height: `|⟨β, y⟩| ≤ D + E m`, where `D = Σ_β Σ_{r ∈ R} |⟨β, r⟩|` and
     `E = Σ_β Σ_a |⟨β, gen_a⟩|`. So `σ(g) ≤ C_σ(1 + D + E m)`, hence
     `1 + σ(g) ≤ (1 + max(C_σ, 0)(1 + D + E))(1 + m)`.
  6. `isRapidlyDecreasingOn_of_geometric` concludes.
- `rationalSquareIntegrableRapidDecay`: introduces the data of the statement and applies the
  previous theorem.

## Scope

- The theorem is exactly the Library's `RationalSquareIntegrableRapidDecayStatement`: rapid decay
  on `G¹` of the coefficients of representations square integrable modulo `A_G(F)`, under the two
  structural premises of that statement. The existence of `K0` with these premises, and the
  consequence "square integrable implies tempered" (III.2), are not treated here.
- Provenance: the main theorem is Waldspurger's Corollary III.1.2. `exists_le_mul_of_compact_translates`
  is Lemma II.1.2 (with `d = 0`) on compact translates. The other declarations of this module are
  internal glue for the route described above.
