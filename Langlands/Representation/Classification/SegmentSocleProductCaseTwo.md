# Case 2 of Zelevinsky's proof of Theorem 6.2

Module `Langlands.Representation.Classification.SegmentSocleProductCaseTwo`,
namespace `Langlands.Classification.SegmentSocleProductCaseTwo`.

Let `π = ⟨Δ_1⟩ × π°` with `π° = ⟨Δ_2⟩ × ⋯ × ⟨Δ_r⟩`, where the segments
satisfy the endpoint condition of Ze80 Theorem 6.2 (`ρ_j ≠ ν ρ'_i` for
`i < j`, with `Δ_i = [ρ_i, ρ'_i]`). BZ77 4.13(a) gives a short exact sequence
`0 → σ → π|P → τ = ⟨Δ_1⟩ × (π°|P) → 0`. The main theorem
`caseTwoExclusion` says: if `π°|P` is homogeneous, no nonzero representation
injects both into `π|P` and into `τ`. In Lean this is the predicate
`SegmentSocleProductHomogeneityInduction.CaseTwoExclusion`, i.e. the premise
`hC2` of the induction in that module. This is Case 2 of BZ77 4.15 in
Zelevinsky's adaptation, which ends with a contradiction to the endpoint
condition.

## Hypotheses

None of these is proved here. `hC` and `hH` are written out inline. The
statement of `hH` is not yet in the Library; the statement of `hC` was
published after this module was written (see below).

| Hypothesis | Proposition | Source |
| --- | --- | --- |
| `hE` | `Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T` | exactness of `Ψ⁻`, `Φ⁻` (BZ77 3.2) |
| `hLD` | `LeftMixedProductDerivative.{uF, max uF uV} F T` | BZ77 4.14(a) |
| `hH` | inline (Ze80 5.3 at `ψ`) | Ze80 5.3 |
| `hC` | inline (support shift at `ψ`) | BZ77 4.7(b), Ze80 4.5 |
| `hF` | `SegmentSocleProductHighestDerivative.{uF, uV} F T` | highest derivative of a segment-socle product (Ze80 3.5 with BZ77 4.6) |

`hE` is in `Derivative.MirabolicMinusExactnessStatement`, `hLD` in
`Derivative.MixedProductDerivativeStatement`, and `hF` in
`Classification.SegmentSocleDerivativesStatement`. All three are published.

`hH` is the same inline hypothesis as in
`SegmentSocleProductHomogeneityInduction`: the left mixed product of any
representation of `GL_k` with a homogeneous representation of `P_(r+1)` is
homogeneous. It is the instance at `ψ` of the draft statement
`LeftMixedProductHomogeneity` (task `49d8eea3-1f52-4505-bfce-d76bf8ed5b8a`).

`hC` is the instance at `ψ` of the statement
`Langlands.Classification.CuspidalProductMirabolicSupportShift`, published
in module `Classification.CuspidalProductMirabolicSupportShiftStatement`
(statement task `d54cc845-00d9-44be-bff2-c7a8bf032d31`; Library commit
`7114a390`). The inline hypothesis is the body of that published proposition
at `ψ`; only the namespace qualification of names differs. The planned
final assembly (not part of this submission) passes the published
statement's instance at `ψ`. In words: let
`ρ_1, …, ρ_r` be cuspidal data with ranks adding to `N + 1`, represented by
actual supercuspidal representations `A_i`. Let `W` be a representation of
`P_(N+1)` (carrier in `Type (max uF uV)`) with an injective intertwiner into the
restriction of `A_1 × ⋯ × A_r` (published `cuspidalProductInduced`). Let
`level W = k > 0`. Then for every irreducible subrepresentation `σ` of
`W^(k)` (published `mirabolicDerivativeOfOrder`) and every supercuspidal
support `s` of `σ` (published `IsSupercuspidalSupport`),
`s.map (CuspidalDatum.twist 1) ≤ ρ_1 + ⋯ + ρ_r` as multisets. This is
BZ77 Lemma 4.7(b) for a submodule of the restriction of a cuspidal product,
used as in Ze80 4.4–4.5.

The proof also calls one published proved theorem,
`cuspidalIntegralTwistFreeness F T` (module
`Classification.CuspidalIntegralTwistFreenessProof`): for a cuspidal datum `ρ`
and an integer `k`, `ν^k ρ = ρ` only if `k = 0`.

## Provenance

Ze80 §6.3 (3), printed p.189 (`zelevinsky-1980-induced-ii`): "In Case 2 of
[I], 4.15 one has to use the reasoning of 4.5 which leads to the equality
`ρ_i ≃ ν ρ'_1`. This contradicts the assumptions of 6.2." Case 2 of BZ77 4.15
(`bernstein-zelevinsky-1977-induced-i`, printed p.459) is the case where a
nonzero submodule of `π|P` embeds into `τ`. There BZ77 compares supports by
Lemma 4.7(b).

The implemented argument is internal derived material and follows this
outline. Let `W ≠ 0` inject into `π|P` and into `τ`. Let `λ°` be the level of
the homogeneous `π°|P`. By 5.3, `τ` is homogeneous of level `λ°`, so `W` has
level `λ°`. Then `W^(λ°)` embeds into `τ^(λ°) ≅ ⟨Δ_1⟩ × π°^(λ°)` (BZ77
4.14(a)), and `π°^(λ°) ≅ ⟨Δ_2⁻⟩ × ⋯ × ⟨Δ_r⁻⟩` (`hF`). So an irreducible
subrepresentation of `W^(λ°)` has support `Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻` (each
segment read as the multiset of its members). Since `W` embeds into
`π|P ⊆ (ρ-product)|P`, the support shift `hC` gives
`ν · (Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻) ≤ Δ_1 + ⋯ + Δ_r`.
`SegmentContentShift.not_map_twist_le` shows that this multiset inequality
forces some `Δ_j` with `j ≥ 2` to begin at `ν · e(Δ_1)`, or `Δ_1` itself to
begin at `ν · e(Δ_1)`. The first is excluded by the endpoint condition (this
is Ze80's `ρ_i ≃ ν ρ'_1`), the second by integral twist freeness.

Ze80 reaches the equality `ρ_i ≃ νρ'_1` through "the reasoning of 4.5". The
Lean proof instead uses the explicit multiset bookkeeping of
`SegmentContentShift`, with the derivative of `π°` given by `hF`.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`, `T : F.TopologicalData` and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology` are fixed, with
`T.topology` installed. Representations of the general linear and mirabolic
groups here have carriers in `Type (max uF uV)`. `EmbedsCuspidal T X S` is the
predicate of `SegmentProductCuspidalEmbedding`: `X` has an injective
intertwiner into an actual product of supercuspidal representatives of cuspidal
data with multiset `S`. `Δ.cuspidalContent` is the multiset of members of `Δ`.
`generalLinearRankCast`, `mirabolicRankCast`, `restrictedProduct`,
`restrictionQuotient`, `tail`, `headIndex`, `headRank` and `tailRank` are as in
`SegmentSocleProductHomogeneityInduction`.

## Declarations

### Rank transports (section `Casts`)

- `embedsCuspidal_of_rankCast hab hX`: if the `GL` rank transport of `X`
  along `hab : a = b` satisfies `EmbedsCuspidal` with `S`, so does `X`.
- `binary_rankCast_obj ha hb h A B`: the binary normalized product of the rank
  transports of `A` and `B` equals (as an object) the rank transport of
  `A × B`.
- `mirabolicDerivativeOfOrder_rankCast_obj ψ h hka hkb c X`: the order-`k`
  derivative of the mirabolic rank transport of `X` equals the `GL` rank
  transport of the order-`k` derivative of `X`.
- `nontrivial_of_isSegmentSocle h`: a segment socle is nonzero, since it is
  irreducible.

### Products with a segment socle in front (section `Cons`)

- `consDatum Δ D d'` (definition): the segment-product datum with first
  segment `Δ` and first block `D`, followed by the segments and blocks of `d'`.
  `consDatum_hasSegmentSocles`: if `D = ⟨Δ⟩` and `d'` has segment socles,
  so does `consDatum Δ D d'`. `consDatum_cuspidalContent`: its cuspidal
  content is `Δ.cuspidalContent + d'.multisegment.cuspidalContent`.
- `embedsCuspidal_socle Δ D hD`: `⟨Δ⟩` satisfies `EmbedsCuspidal` with
  `Δ.cuspidalContent` (the one-segment datum, `embedsCuspidal_induced` and
  `nonempty_iso_single`).
- `exists_injective_rightZero ha hc hac A Y hY`: if the second rank `c` is `0`
  and `Y` is one-dimensional, the binary product `A × Y` injects into the rank
  transport of `A`. Proof: for `c = 0` the published binary product is the
  universe lift of `A ⊗ Y` with the action of `GL_(a+0)` reindexed to `GL_a`.
  The map is `A ⊗ Y ≅ A ⊗ ℂ ≅ A`.
- `embedsCuspidal_binary_cons Δ D hD d' hd' hl`: for a nonempty datum `d'`
  with segment socles, `⟨Δ⟩ × d'.induced` satisfies `EmbedsCuspidal` with
  `Δ.cuspidalContent + d'.multisegment.cuspidalContent` (via `consDatum` and
  `nonempty_iso_binary`).
- `embedsCuspidal_binary_nil Δ D hD d' hl Y hY`: the same for an empty datum
  `d'`, with a one-dimensional second factor `Y` on `GL_c` (then `c = 0`).

### The support bound (section `Core`, hypotheses `hE hLD hH hC`)

`support_shift_le hl D P hD hP hlev S S' hS hS' W f g hf hg hW`: let `D` be
nonzero on `GL_(m+1)` and `P` on `GL_(n+1)`, and let `P|P` be homogeneous of
level `l`, with `0 < l ≤ n + 1`. Assume:

- `hS`: the rank transport of `D × P` satisfies `EmbedsCuspidal` with `S`;
- `hS'`: `D × (P|P)^(l)` satisfies `EmbedsCuspidal` with `S'`, where
  `(P|P)^(l)` is the published order-`l` derivative on `GL_(n+1-l)`;
- `W` is nontrivial with injective intertwiners `f` into
  `(restrictedProduct T m n).obj (D, P)` and `g` into
  `(restrictionQuotient T m n).obj (D, P)`.

Then `S'.map (CuspidalDatum.twist 1) ≤ S`.

Proof. By `hH`, the left mixed product `X = D × (P|P)` is homogeneous. The
quotient `restrictionQuotient` is its mirabolic rank transport, so it is
homogeneous too (`RightMixedLevel.isHomogeneous_mirabolicRankCast`). By
`RestrictedProductLevel.level_leftMixed_le` and `le_level_leftMixed`
(with `hLD`, `D ≠ 0`), `level X = l`. So `level W = l`
(`LevelCalculus.level_eq_of_isHomogeneous`), and `W^(l) ≠ 0`. By exactness
(`hE`, `LevelCalculus.map_injective_of_exact`), `W^(l)` injects into the
order-`l` derivative of the quotient. That derivative is the rank transport
of `X^(l)`, and `X^(l) ≅ D × (P|P)^(l)` by the first part of `hLD`. So
`W^(l)` satisfies `EmbedsCuspidal` with `S'`, and by
`EmbedsCuspidal.exists_irreducible` it has an irreducible subrepresentation
`σ` that does too; hence `σ` has supercuspidal support `S'`. From `hS`, `f`
composed with the restriction of the cuspidal embedding is an injective
intertwiner of `W` into the restriction of a supercuspidal product with
multiset `S`. Then `hC` gives `S'.map (twist 1) ≤ S`.

### The exclusion (section `Exclusion`, hypotheses `hE hLD hH hC hF`)

- `exclusion_of_head_tail Δ D₀ hD₀ td htl htd ha hb hsep hP hS`: let
  `D₀ = ⟨Δ⟩` on `GL_(deg Δ)` with `deg Δ = m + 1`, and let `td` be a datum of
  rank `c = n + 1` and length `k + 1` with segment socles. Assume:
  - `hsep`: no segment of `td` begins at `ν · e(Δ)`;
  - `hP`: the restriction of `td.induced` is homogeneous;
  - `hS`: the rank transport of `D₀ × td.induced` satisfies `EmbedsCuspidal`
    with `Δ.cuspidalContent + td.multisegment.cuspidalContent`.

  Then no nontrivial `W` injects both into the restricted product and into
  the quotient (as in `CaseTwoExclusion`). Proof. Let `l` be the sum of the
  ranks of the segments of `td`, so `0 < l ≤ c`. By `hF`, derivatives of
  `td.induced` above order `l` vanish, and `td.induced^(l) ≅ d'.induced`,
  where `d'` has segments `Δ_j⁻` (singletons dropped) and segment socles.
  This derivative is nonzero: if `d'` is empty, every segment of `td` is a
  singleton and `hF` makes it one-dimensional; otherwise it is a product of
  nonzero socles (`ProductVanishing.nontrivial_normalizedProduct`). So the
  restriction of `td.induced` has level `l` (`RestrictionBridge`, published
  `level_eq_iff`). `embedsCuspidal_binary_nil` and
  `embedsCuspidal_binary_cons`, transported along the isomorphism of `hF`,
  give `hS'` with `S' = Δ.cuspidalContent + d'.multisegment.cuspidalContent`.
  `support_shift_le` then gives
  `ν · (Δ + ∑ Δ_j⁻) ≤ Δ + ∑ Δ_j` (contents). This contradicts
  `SegmentContentShift.not_map_twist_le`, applied with the published theorem
  `cuspidalIntegralTwistFreeness F T` and `hsep`.
- `exclusion_of_head_tail_of_eq`: the same statement with the head block on
  `GL_a` for some `a` equal to `deg Δ`. This is Lean packaging. It avoids an
  expensive definitional unfolding of `d.shape.headRank h` against
  `Δ.degree`.
- `caseTwoExclusion d h m n ha hb hd hsep hP` (main theorem): for
  `h : d.length = k + 2`, `d.HasSegmentSocles`, the endpoint condition `hsep`
  of Theorem 6.2, and homogeneity `hP` of the restriction of
  `(tail d h).induced` transported to `GL_(n+1)`,
  `CaseTwoExclusion T d h m n ha hb` holds. Proof: `embedsCuspidal_induced`
  for `d`, transported along `nonempty_iso_binary` and with the content split
  by `ofFn_segments_eq_cons`, gives `hS`. `head_endpoint` gives `hsep` for the
  tail. Then apply `exclusion_of_head_tail_of_eq`.

## Import audit

See the import audit in `SegmentSocleProductHomogeneityInduction.md`, which
covers this module and that one together.
