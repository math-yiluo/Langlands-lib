# Proof: the rational classification of standard parabolics

Author: Worker 3789 (formerly Worker 28).

`theorem Langlands.GroupScheme.standardParabolicClassification :
StandardParabolicClassificationStatement.{u}` proves the published target of
`Rational/StandardParabolicClassificationStatement` at an arbitrary universe `u`. The
hypotheses are exactly those of the target: every field `k : Type u`, every connected
reductive `G`, every maximal split torus `i : T ⟶ G` and every cocharacter `ν` with
`IsGenericCocharacter i ν`. No characteristic, perfectness, splitness, reducedness or
positive-rank assumption is added. Anisotropic groups and an empty set of simple roots
need no separate argument.

In the target, `P(ν)` is the dynamic parabolic of `ν ≫ i`, which the target's Markdown
calls the minimal parabolic. The Lean target does not assert this minimality among rational
parabolic functors (`GenericMinimalParabolicStatement`), and the proof does not use it.

## Route

The final theorem feeds four inputs to the published conditional assembly
`standardParabolicClassification_of_local_inputs`
(`Rational/StandardParabolicClassificationReduction`):

1. standardness by containment,
2. a rational conjugate of every cocharacter whose dynamic parabolic contains `P(ν)`,
3. injectivity of `J ↦ P_J`,
4. rigidity: rationally conjugate standard parabolics are equal.

The published conditional theorem
`standardParabolicClassificationStatement_of_structural_statements` needs
`SmoothMaximalSplitTorusConjugacyStatement` and `RelativeTitsSystemStatement`. This proof
uses neither. In their place it uses the rational Bruhat decomposition `rationalBruhat`
(`Rational/RationalBruhatProof`), the lemma `exists_parabolic_conj_into_torus`
(`Rational/GenericParabolicCocharacterConjugacy`) and the published trivial positive-root
stabilizer `hasTrivialPositiveRootStabilizer`.

The two Bruhat modules are by Worker 3784 and ship in this candidate as supporting modules,
with their own Markdown. Their Lean files are byte-identical to Worker 3784's candidate
`c49967d0-5e5e-4bde-a476-646efa96a191`. That candidate was rejected because Task 3784 also
requires the generic-minimality identification, and these modules do not provide it. The
review found no defect in their proofs. Minimality is not used here.

Other published inputs: `relativeRootSignInclusions`, `relativeRootNegation`,
`genericCentralizer`, `standardParabolicEndpoints`, and the standard-cocharacter statement
obtained as `standardCocharacterStatement_of_reflections_of_signs` applied to
`relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization` and
`relativeRootSignsDetermineDynamic`. The relative root system is used as the published
term `relativeRootSystemStatement_of_rootRankOneFactorizationStatement
rootRankOneFactorization`. Input 3, and the inclusion `P_∅ ≤ P_J` used in the rigidity
step, come from the published `standardParabolic_order_of_root_comparison` applied to
`relativeRootNegation`, the standard cocharacters and `relativeRootSignInclusions`. These two
compositions are the same as those in the staged candidates of Worker 3783
(`RelativeRootSystemProof`) and Worker 3787 (`StandardParabolicOrderProof`). They are
written out here so that the proof depends only on published declarations and the Bruhat
modules. The proof also uses the published chamber move
`exists_normalizerPoint_parabolic_le_of_statements`, the face lemma
`exists_standardParabolic_eq_of_parabolic_le_of_statements`, and the flag-quotient tools
behind `rationalBruhat`: the published `smoothSubgroupQuotientExistence`,
`parabolicSubgroupQuotientProper`, `Dynamic.flagQuotientSchemeAction`,
`AffineLine.exists_extension_of_isProper` and `range_conjugate_le_of_fixed_coset`, and
`exists_rational_lift_of_dynamicParabolic` from `Rational/RationalBruhatProof`.

Notation: `int(g)` is `(G.innerIso g).hom`, so `F.comap int(g)` consists of the points `x`
with `g x g⁻¹ ∈ F`. `n · ξ` is `cocharacterAut (normalizingAut i n) ξ`. `B` is `P(ν)`, the
dynamic parabolic of `ν ≫ i`. A cocharacter `λ` of `T` is *dominant* when
`0 ≤ ⟨α, λ⟩` for every relative root `α` with `0 < ⟨α, ν⟩`.

## Steps

**Cocharacters into the torus.** `exists_innerIso_comp_eq_torus_of_represented` works with
arbitrary closed representatives of `P(ν)` and of the opposite contracting subgroup.
`exists_innerIso_comp_eq_torus_cocharacter` specializes it to the affine representatives;
the hypothesis on the dynamic centralizer comes from `genericCentralizer`. Let `zeta` be a
cocharacter of `G`. The homogeneous quotient `G/P(ν)` is proper. The `zeta`-orbit of the base
coset extends over the affine line, and its value at `0` is a `zeta`-fixed point. A rational
lift `h₀` of this point gives `range(zeta ≫ int(h₀⁻¹)) ≤ P(ν)`.
`exists_parabolic_conj_into_torus` then provides `p ∈ P(ν)(k)` and `ρ : 𝔾ₘ ⟶ T` with
`zeta ≫ int(p h₀⁻¹) = ρ ≫ i`. These steps follow the proof of
`exists_bruhat_factorization_of_represented`, with `zeta` in place of `ν ≫ i` and the base
coset in place of the coset of a point `g`.

**Dominant representative.** `exists_innerIso_comp_eq_dominant_cocharacter` follows this with
the chamber move: there are `g` and a cocharacter `ξ` of `T` with
`zeta ≫ int(g) = ξ ≫ i` and `B ≤ P(ξ ≫ i)`. This gives input 2.

**Bruhat reduction.** In `exists_normalizerPoint_comap_of_bruhat`, suppose `B ≤ Q`,
`B ≤ R` and `Q = R.comap int(g)`. Write `g = p n q` with `p, q ∈ B(k)` and `n` normalizing
`i`. Points of a subgroup functor normalize it (`comap_innerIso_hom_eq_of_mem`), so `p` drops
out on the `R` side and `q` on the `Q` side, and `Q = R.comap int(n)`.
`dynamicParabolic_comap_normalizerPoint` gives
`P(ξ ≫ i).comap int(n) = P((n⁻¹ · ξ) ≫ i)`.

**Standardness by containment** (`exists_standardParabolic_eq_of_parabolic_le_of_bruhat`).
Let `B ≤ P(zeta)`. Take `g` and `ξ` as above. Then
`P(zeta) = P(ξ ≫ i).comap int(g)` (`Dynamic.parabolic_eq_comap_of_iso`). Both sides contain
`B`, so the Bruhat reduction gives `P(zeta) = P((n⁻¹ · ξ) ≫ i)`. The face lemma
`exists_standardParabolic_eq_of_parabolic_le_of_statements` identifies this cocharacter
parabolic with a standard `P_J`, `J ⊆ Δ`. This gives input 1.

**Chamber move in a stabilizer** (`HasRelativeRootSystem.exists_normalizerPoint_fixing_nonneg`).
Let `ρ` be the sum of the positive relative roots of `ν`. Over the normalizing points `u`
fixing every root pairing `⟨β, u · ξ⟩ = ⟨β, ξ⟩`, the value `⟨ρ, u · η⟩` takes finitely many
values; choose `u` maximizing it. Suppose a positive root `α` orthogonal to `ξ` has
`⟨α, u · η⟩ < 0`. A normalizing point `m` acting by a reflection in `α` keeps the pairings of
`ξ`, because `⟨α, ξ⟩ = 0`. The reflection coefficient of `ρ` is positive, so
`⟨ρ, (m⁻¹u) · η⟩` is larger, a contradiction. The positivity argument is that of the
published `exists_normalizerPoint_dominant`, restricted to this subset.

**Dominant orbits** (`HasRelativeRootSystem.latticePairing_eq_of_dominant`). If `λ` and
`n · λ` are both dominant, then `⟨β, n · λ⟩ = ⟨β, λ⟩` for every relative root `β`. Put
`η = n⁻¹ · ν`. Roots positive on `η` are nonnegative on `λ`. Take `u` from the previous step
for `ξ = λ`, and write `η' = u · η`.

- Positive roots orthogonal to `λ` are nonnegative on `η'` by the choice of `u`.
- Roots positive on `λ` are positive on `η'`, using `-Φ = Φ` and the genericity of `η'`.

Hence `η'` lies in the chamber of `ν`. The class of `n u⁻¹` therefore preserves the positive
roots of `ν`, so it is trivial by `hasTrivialPositiveRootStabilizer`. So `n` and `u` act
equally on cocharacters, and `u` fixes the root pairings of `λ`.

**Rigidity** (`standardParabolic_eq_of_isRationallyConjugate_of_bruhat`). Let `J, K ⊆ Δ` and
`P_J = P_K.comap int(g)`. Standard cocharacters `ξ_J`, `ξ_K` give `P_J = P(ξ_J ≫ i)` and
`P_K = P(ξ_K ≫ i)`. Both contain `B` by the order and endpoint statements. The Bruhat
reduction gives `P(ξ_J ≫ i) = P((n⁻¹ · ξ_K) ≫ i)` for a normalizing `n`. By the sign
inclusions, `ξ_K` and `n⁻¹ · ξ_K` are both dominant. The dominant-orbit lemma equates all
their root pairings, and the sign inclusions in both directions give `P_J = P_K`. This gives
input 4.

## Sources

Borel–Tits, *Groupes réductifs* (1965), source `borel-tits-1965-groupes-reductifs`, §5.14
(printed pp.99–100), states both clauses over an arbitrary field: the standard
k-parabolics are the only k-subgroups containing the minimal one, and every k-parabolic is
k-conjugate to exactly one standard k-parabolic. Standard parabolics are defined in §5.12
(p.99). The implemented route is internal and is not a transcription of the
source's argument. It combines three things:

- the Bruhat decomposition (Borel–Tits 5.15, printed p.100), in its Lean form
  `rationalBruhat`;
- Weyl-chamber combinatorics: maximization of `⟨ρ, ·⟩` and the trivial positive-root
  stabilizer;
- a fixed point of a cocharacter on the proper flag variety `G/P(ν)`.

It does not use the relative Tits system or the conjugacy of maximal split tori in smooth
connected groups. The target and its Markdown are unchanged.
