# Nonmultipliable relative coroots of a simply connected group span the cocharacters

`Langlands.GroupScheme.NonmultipliableCorootSpanStatement.{u}` is a statement-only,
`Prop`-valued definition. This module proves nothing and adds no other declarations.

## Statement

For every field `k : Type u`, every group scheme `G` over `Spec k` with
`hG : IsSimplyConnected G`, every commutative group scheme `S` and every
`i : S.toGrp ⟶ G` with `IsMaximalSplitTorus i`, and every Mathlib root datum
`P : RootDatum J (characterLattice S) (cocharacterLattice S)` with `J : Type u`, assume:

1. `P.toLinearMap = latticePairing S`: the pairing of `P` is the actual pairing of characters
   and cocharacters of `S`;
2. `Set.range P.root = {a | a ∈ roots i ∧ (2 : ℤ) • a ∉ roots i}`: the roots of `P` are exactly
   the nonmultipliable relative roots of `i` (`roots i` uses the `IsAffineHom` instance of
   `hG`);
3. for every `α : J` there are a rational point `n` of `G` and an automorphism `σ` of `S` with
   `IsNormalizingPoint i n σ` and `characterAut σ = P.reflection α`: each reflection of `P` is
   the action on characters of a rational point normalizing `i`.

Then `P.corootSpan ℤ = ⊤`: the integral coroots of `P` span the whole cocharacter lattice of
`S`.

Hypotheses 1–3 are the three clauses of `IsRootDatumOf` (module `Reductive.RootDatum`) with the
roots of `i` replaced by the nonmultipliable ones. The reflection of `P` at `α` determines
`P.coroot α`: since the character lattice is torsion-free and `P.root α ≠ 0`, the formula
`χ ↦ χ - ⟨χ, P.coroot α⟩ P.root α` determines `P.coroot α` from the reflection. Hypothesis 3
therefore pins the coroots of `P` to the relative coroots of the nonmultipliable roots, the
coroots of the reduced relative root system `Φ′`. The statement does not assert that such a
`P` exists. Split rank zero is included (then `S` is trivial and the conclusion is automatic).

## Source correspondence

Armand Borel and Jacques Tits, *Compléments à l'article « Groupes réductifs »*, Publications
Mathématiques de l'IHÉS 41 (1972), registered as
`borel-tits-1972-complements-groupes-reductifs` (SHA-256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`):

- Proposition 4.3, printed p.271 (PDF p.20), proof pp.271–272 (PDF pp.20–21). For a semisimple
  `G`, a maximal torus `T` containing a maximal torus `T₁` of a semisimple subgroup `G₁`, the
  restriction `r`, `Φ = Φ(T, G)` and `Φ₁ = Φ(T₁, G₁)`, assuming that `r(Φ)^×` is a root system
  whose nonmultipliable elements are `Φ₁` and that `Φ` has a base `Δ` with
  `r(Δ) ∖ {0}` a base of `r(Φ)^×`: (ii) `P(Φ₁) = r(P(Φ))`. Remark 4.5 b), p.273 (PDF p.22),
  gives the dual form (ii)′ `Q(Φ̌) ∩ V₁′ = Q(Φ̌₁)`, in which form the proposition is proved
  (relation (4) on p.272).
- Corollaire 4.4, p.272 (PDF p.21): if `G` is simply connected then `G₁` is simply connected,
  that is `X*(T₁) = P(Φ₁)`; dually `X_*(T₁) = Q(Φ̌₁)`.
- Corollaire 4.6 (J. Humphreys), p.273 (PDF p.22): the maximal split semisimple subgroup `F` of
  [1965, 7.2] of a simply connected `G` is simply connected, by 4.4 and [1965, 6.8].

For a maximal `k`-torus `T` containing `S`, the compatibility hypotheses of 4.3 with
`T₁ = S` and `Φ₁ = Φ′` are 1965 6.8 (restriction of an adapted absolute base). With `G` simply
connected, `X_*(T) = Q(Φ̌)`, so `X_*(S) = Q(Φ̌) ∩ V₁′ = Q(Φ̌′)` by (ii)′: this is the Lean
conclusion. The source phrases it for a subgroup `G₁`; only its torus and root system enter
(ii)′, so the Lean statement is formulated for `(G, S)` and the root datum `P` alone, without
a subgroup. This formulation is derived: the source has no separate statement for it.

## Use

`Langlands.GroupScheme.simplyConnectedQuasiSplitEnvelope_of_maximalSplitSubgroup`
(module `SimplyConnected.QuasiSplitEnvelopeReduction`) applies this statement to the root
datum of the split subgroup of Borel–Tits 7.2.
