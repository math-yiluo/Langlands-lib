# The positive support shift of an irreducible highest derivative (BZ77 4.7(b))

Authors: Worker 818 (this pair and the helper pair
`CuspidalProductDerivativeQuotientSupport`) and Worker 128 (the helper pair
`HighestDerivativeSupportShiftBoundary`).

This module proves the theorem `Langlands.Classification.highestDerivativeSupportShift`
(line 733). Its type is exactly the published proposition
`Langlands.Classification.HighestDerivativeSupportShift.{uF,uV} F T` from
`Langlands.Representation.Classification.SegmentSocleDerivativesStatement`:

```lean
theorem highestDerivativeSupportShift {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : HighestDerivativeSupportShift.{uF, uV} F T
```

The target pair and every pair it imports are unchanged. The module adds no axioms
and no proposition definitions, and it has no `sorry`, `admit` or `set_option`.
The theorem has no premise beyond the target's own telescope. A Lake build of the
workspace has 0 errors and 0 warnings, and `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`. The universe parameters are exactly `uF uV`.
All auxiliary declarations are in the namespace
`Langlands.Classification.HighestDerivativeSupportShiftProof`.

## The statement proved

Fix a prime `p`, a `p`-adic field `F : PadicField.{uF} p` and supplied topological data
`T`. All topology is `T.topology`. The statement quantifies over every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`. No additive-character
existence is assumed. It then quantifies over every `n`, every
`ω : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)` and every order
`k ≤ n`. Assume:

- `ω` is irreducible;
- the actual derivative `(Derivative.generalLinearDerivative T ψ n k hk).obj ω` is
  nontrivial;
- every derivative of order `j` with `k < j ≤ n` is subsingleton.

Then for every `σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier)`
that is an actual irreducible subrepresentation of that derivative
(`IsIrreducibleSubrepresentation`), and all multisets `s s'` of
`CuspidalDatum.{uV, uF}` with `T.IsSupercuspidalSupport ω s` and
`T.IsSupercuspidalSupport σ s'`, we have

`s'.map (CuspidalDatum.twist 1) ≤ s`

as multisets. Multiplicities count, and the twist is the positive `ν = |det|^1`. The
proof covers every order `k ≤ n` allowed by the statement:

- `k = n`, including `n = 0`, is the rank-zero boundary;
- `k = 0` with `0 < n` is excluded by the hypotheses;
- `0 < k < n` is the main case.

No level witness is chosen. The field universe `uF` and the datum carrier universe
`uV` stay independent. Representations of `GL` have carrier universe `max uF uV`, as
in the target. Supercuspidal representatives `A i` have carrier universe `uV`.
The published 3.8 pairing is used at universes `.{uF, max uF uV, max uF uV}`.

## Normalization and topology

The derivative is the published `Langlands.Derivative.generalLinearDerivative`, used
unchanged with its determinant inverse-half normalization. Section `Bridge`
(lines 23–62) proves `generalLinearDerivative_obj_eq`: for `0 < j ≤ N + 1`, the
order-`j` derivative of `X` on `GL_(N+1)` equals
`(Derivative.mirabolicDerivativeOfOrder T ψ N j _).obj` applied to the restriction
`(Derivative.generalLinearRestriction T N).obj X`. The proof unfolds the published
definition and removes rank casts (`restriction_rankCast`). It is an equality of
objects, so both sides carry the same normalization. The published 3.8 pairing
statement is formulated for exactly this mirabolic derivative of a restriction. No
second normalization is introduced.

The pairing `β` built in section `Pairing` has covariance
`g ↦ T.determinantNorm (N+1) g` (as a complex number). That is the covariance required
by the published statement `Derivative.MirabolicHighestDerivativePairingStatement`.
It is obtained from `T.determinantPowerCharacter (N+1) 1` by `coe_realPowerCharacter`
and `Real.rpow_one`. No Haar measure or modulus character appears in this proof. The
dual and the character twist of a normalized product come from published theorems
(`twistedProductOrdinaryDual`, `twistedProductCharacterTwist`), stated for the
Library's normalized induction. Hence no Haar-modulus comparison is needed, and the
comparison tasks `a622f240-4846-4086-b34f-f650ba636ee4` and
`f947a735-872d-44db-a9ea-954d17dec4bd` are not used.

The real-power character `ν^t` of `F^×` (`unitsPowerCharacter`, line 191) is
`realPowerCharacter T.normalizedAbsUnits t`. It uses `T.valuativeRel` and `T.localField`
only to name that character. The topological group structure on each `GL_m` is the
supplied `T.generalLinearTopologicalGroup m`.

## Proof, section by section

Write `Π = A_1 × ⋯ × A_r` for `T.cuspidalProductInduced ρ h A`, the Library's
normalized product of supercuspidal representatives `A i` of data `ρ i` with rank
sum `n`. Write `X̃` for the smooth contragredient.

**Contragredient (lines 64–87).** `smoothContragredientEquiv`: an equivalence
`ρ ≃ σ` of representations gives `σ̃ ≃ ρ̃` through `contragredientMap`.

**Data (lines 89–175).**

- `dualDatum ρ` is the datum of `ρ̃`. Its class is `T.supercuspidalClassContragredient`,
  which is well defined by the published `GeneralLinear.supercuspidalContragredient`.
- `dualDatum_dualDatum` is involutivity.
- `dualDatum_twist`: `(ν^s ρ)~ = ν^(-s) ρ̃`. It uses the published
  `SupercuspidalClass.contragredient_twist`, `SupercuspidalClass.twist_congr` and
  `realPowerCharacter_neg`.
- `twistedDualData t ρ` is the family `ν^t ρ̃_i`. Its class `twistedDualClass` is marked
  `@[irreducible]` only to keep elaboration fast.
- `twistedDualRep t ρ A` is the family of representatives `ν^t Ã_i`, built with
  `SupercuspidalRep.twist (T.determinantPowerCharacter _ t)` and
  `SupercuspidalRep.contragredient`.
- `twistedDualRep_represents` checks that these representatives represent
  `twistedDualData t ρ`.

**ProductDual (lines 177–424).** The main construction is
`twistedDualEquiv hn t ρ h A`. For `0 < n` it is an equivalence of representations of
`GL_n`:

`ν^t Ã_1 × ⋯ × ν^t Ã_r ≃ twist (T.determinantPowerCharacter n t) Π̃`.

It is a composite of these equivalences:

- `productZeroEquiv`: `Π ≃ i(ν^0 A_1, …, ν^0 A_r)`, by the published
  `normalizedProductInducedEquiv`;
- `ordinaryDualEquiv`: the dual of `i(ν^0 A_i)` is `i(ν^(-0) Ã_i)`. This is the
  published `twistedProductOrdinaryDual`, which needs `0 < n` and the admissibility
  of every `A i`;
- `characterTwistEquiv`: twisting by `ν^t ∘ det` twists every block. This is the
  published `twistedProductCharacterTwist`, with `unitsPowerCharacter_comp`
  identifying `ν^t ∘ det` with `T.determinantPowerCharacter n t`;
- `twistedDualBlockEquiv` and `twistedProductBlocksEquiv`, which identify the blocks
  with the representatives `twistedDualRep t ρ A`;
- `twistedDualShapeIso := Iso.refl _`. This is a definitional isomorphism, used so
  that the kernel compares objects rather than carrier types.

**Quotient (lines 426–513).** Let `γ` be an invariant form on `ρ × π` with trivial
covariance, and let `j : σ → ρ` be an intertwiner. Then `pairingMap` is the
intertwiner `π → σ̃` given by `w ↦ (u ↦ γ (j u) w)`. Its values are smooth because
`π` is smooth. `pairingMap_ne_zero` shows it is nonzero when:

- `γ` is nondegenerate in its first argument,
- `j` is injective, and
- `σ` is irreducible, so it has a nonzero vector (the published
  `CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible`).

**Pairing (lines 515–570).** `exists_restricted_pairing`: let `ι : ω → P` be injective
and let `e : P' ≃ twist (|det|^1) P̃`. Then `β v w = (e w)(ι v)` is a form on the
mirabolic restrictions of `ω` and `P'`. Its covariance is
`g ↦ T.determinantNorm (N+1) g`, and it is nondegenerate in `ω`. Nondegeneracy uses
the published `smoothBidual_injective_of_compact_cofinal`, which says that a smooth
representation embeds into its smooth bidual, together with the injectivity of `ι`.

**Support (lines 572–609).**

- `ofFn_twistedDualData` rewrites the support of `twistedDualData t ρ` as
  `(List.ofFn ρ).map (fun x => (dualDatum x).twist t)`.
- `support_shift`: if `s'.map (x ↦ ν^0 x̃) ≤ s.map (x ↦ ν x̃)`, then
  `s'.map (twist 1) ≤ s`. The proof applies the multiset map `y ↦ ν ỹ` to both sides
  and uses `dualDatum_twist`, involutivity, `CuspidalDatum.twist_twist` and
  `CuspidalDatum.twist_zero`.

**DualSupport (lines 611–659).** `isCuspidalConstituent_contragredient`: let
`σ ↪ ρ_1 × ⋯ × ρ_r` be an injective intertwiner into a cuspidal product of positive
rank `m`, and suppose `σ̃` is irreducible. Then `σ̃` is a cuspidal constituent of
`twistedDualData 0 ρ`, the family `ν^0 ρ̃_i`. The dual map of the embedding is
surjective by the published `contragredientMap_surjective_of_injective_of_compact_cofinal`
(exactness of the smooth dual). Composing it with `twistedDualEquiv` at `t = 0` and
with `|det|^0 = id` gives a quotient map from `ν^0 ρ̃_1 × ⋯ × ν^0 ρ̃_r` onto `σ̃`.

**Main (lines 661–721).** `exists_derivative_map` implements BZ77 4.8(b). Let `ω` on
`GL_(N+1)` have nontrivial order-`k` derivative, `0 < k`, and vanishing higher
derivatives. Let `ι : ω ↪ Π`, and let `σ` be irreducible with `j : σ ↪ ω^(k)`.

1. Let `Π̄ = ν Ã_1 × ⋯ × ν Ã_r`, a cuspidal product for `twistedDualData 1 ρ`. Apply
   `exists_restricted_pairing` to `ι` and to `twistedDualEquiv` at `t = 1`. The result
   is a pairing `β` between the mirabolic restrictions of `ω` and `Π̄` with covariance
   `|det|`, nondegenerate in `ω`.
2. Translate the derivative hypotheses with `generalLinearDerivative_obj_eq`, and apply
   the published `Derivative.mirabolicHighestDerivativePairing.{uF, max uF uV, max uF uV}`
   (BZ77 Proposition 3.8). It gives an invariant pairing `γ` between `ω^(k)` and
   `Π̄^(k)`, with trivial covariance and nondegenerate in `ω^(k)`.
3. `pairingMap` then gives a nonzero intertwiner `χ : Π̄^(k) → σ̃`.

**Final theorem (lines 733–771).**

- If `k ≥ n`, then `k = n` and `σ` lives on `GL_0`. Worker 128's
  `IsSupercuspidalSupport.twist_le_of_rank_zero` shows that `s' = 0`, which gives the
  claim.
- Otherwise `0 < n`, and `Derivative.highestGeneralLinearDerivativeOrder_pos`
  (Worker 128) gives `0 < k`. Write `n = N + 1`.
- `glSupercuspidalEmbedding` embeds `ω` into some `Π = ρ_1 × ⋯ × ρ_r`.
  `glSupercuspidalSupportUniqueness` gives `List.ofFn ρ = s`.
- `CuspidalSupport.cuspidalEmbedding` (first component) shows that `σ` is admissible.
  `SmoothRep.isIrreducible_contragredient_iff` then shows that `σ̃` is irreducible.
- `exists_derivative_map` gives the nonzero `χ : Π̄^(k) → σ̃`.
- The helper `CuspidalProductDerivativeQuotientSupport.derivative_quotient_support`,
  applied to the data `twistedDualData 1 ρ` with representatives `twistedDualRep 1 ρ A`
  and to `τ = σ̃`, gives `ρ''`. Here `σ̃` is a cuspidal constituent of `ρ''`, and
  `List.ofFn ρ'' ≤ List.ofFn (twistedDualData 1 ρ)`.
- Embed `σ ↪ ρσ_1 × ⋯ × ρσ_l` (`glSupercuspidalEmbedding`). Uniqueness gives
  `List.ofFn ρσ = s'`. `isCuspidalConstituent_contragredient` makes `σ̃` a constituent
  of `twistedDualData 0 ρσ`. Uniqueness for `σ̃` then identifies `List.ofFn ρ''` with
  `List.ofFn (twistedDualData 0 ρσ)`.
- Rewriting with `ofFn_twistedDualData` gives
  `s'.map (x ↦ ν^0 x̃) ≤ s.map (x ↦ ν x̃)`, and `support_shift` concludes.

## Comparison with the original proof

Sources:

- Bernstein–Zelevinsky (1977), literature ID `bernstein-zelevinsky-1977-induced-i`,
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Lemma
  4.7(b) is on printed p.455 (zero-based PDF index 15). Its proof is §4.8: part (a) is
  the first sentence of §4.8 on printed p.455, and part (b) runs over printed
  pp.455–456 (zero-based PDF indices 15–16). Proposition 3.8 is on printed p.453
  (zero-based PDF index 13). The definition of a `χ`-pairing is in §3.6, printed
  p.452.
- Zelevinsky (1980), literature ID `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Its 4.4(d) on
  printed p.185 reads `νφ_ω − φ_σ ≥ 0` with `(νφ)(ρ) = φ(νρ)`. In multiset form that
  is `s'.map (twist 1) ≤ s`, the positive twist of the target.

BZ77 4.7(b) concerns a nonzero `P`-submodule `ω` of `π = ρ_1 × ⋯ × ρ_r` with highest
derivative `ω^(k)`, and an irreducible submodule `σ ⊆ ω^(k)`. It asserts
`ν · supp σ ⊂ (ρ_1, …, ρ_r)`. The proof in §4.8(b) proceeds as follows:

- Set `π̄ = ν π̃ = ρ̄_1 × ⋯ × ρ̄_r` with `ρ̄_i = ν ρ̃_i` (2.3(d), 1.9(f)).
- The natural `1`-pairing of `π̃` and `π` induces a `ν⁻¹`-pairing of `π` and `π̄`.
  Restricting it to `P` gives a nondegenerate `Δ`-pairing of `π|_P` and `π̄|_P`, and
  restricting further to `ω` gives a `Δ`-pairing nondegenerate with respect to `ω`.
  Here BZ77 §3.6 (printed p.452) calls a form `B` a `χ`-pairing when
  `χ(g) · B(π_1(g)v, π_2(g)w) = B(v, w)`. So the `ν⁻¹`-pairing satisfies
  `B(gv, gw) = ν(g) · B(v, w)`, with `ν = |det|`. The Library's
  `InvariantBilinear.forms ρ σ c` uses the opposite side, `β (ρ g v) (σ g w) =
  c g * β v w`. So a source `χ`-pairing is a Library form with covariance `χ⁻¹`, and
  the source `ν⁻¹`-pairing is a Library form with covariance `|det|`. This is the
  covariance `T.determinantNorm (N+1)` of the form built by `exists_restricted_pairing`
  (lines 523–568). It is also the covariance in the hypothesis of the published 3.8
  statement, whose Markdown explains why the source `Δ_P = |det|⁻¹` gives this sign.
  The positive twist `ν` in `π̄ = ν π̃` is not changed by this bookkeeping.
- By 3.8 the induced pairing of `ω^(k)` and `π̄^(k)` is nondegenerate with respect to
  `ω^(k)`. Restricting to `σ` shows that `σ̃` is a Jordan–Hölder constituent of
  `π̄^(k)`.
- Since `ρ̄_i` is cuspidal, part (a) gives `supp σ̃ ⊂ (ρ̄_i)`, hence
  `supp σ ⊂ (ν^(-1) ρ_i)`.

The Lean proof follows this route step by step: `twistedDualEquiv` at `t = 1`, then
`exists_restricted_pairing`, then the published 3.8, then `pairingMap`, then the
helper, then `isCuspidalConstituent_contragredient` and `support_shift`. It differs
in these implementation details:

- The target has an irreducible `ω`. The proof embeds `ω` into a cuspidal product by
  the published `glSupercuspidalEmbedding` and identifies `s` by published uniqueness
  (BZ77 §4.1 / Ze80 4.4 transfer). The same is done for `σ`.
- "`σ̃` is a constituent of `π̄^(k)`" is used in quotient form: there is a nonzero
  intertwiner `π̄^(k) → σ̃`.
- Part (a) is the helper `derivative_quotient_support`, a quotient form of BZ77
  4.7(a). It is proved through the published Ze80 3.7(b) partial-derivative/Jacquet
  comparison and the published geometric lemma, not through the Leibniz filtration
  of BZ77 4.5/4.6. The helper Markdown has the details.
- `supp σ̃ = (supp σ)~` is proved by dualizing an embedding of `σ`, using exactness of
  the smooth dual. BZ77 uses the corresponding fact without proof.
- Supports are multisets throughout, so multiplicities are kept.

The project's source and errata pointers contained no applicable correction for these
passages. This records a bounded check, not an assertion that no erratum exists.

## Published helper pairs

Two helper pairs written for this task are imported by their Lean names. Each was
independently reviewed and published as a `lean.definition` artifact before this
proof was submitted, and neither is part of this candidate:

- `Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport`
  (Worker 818): definition `bf38b454-70f8-4bf4-83b2-0def96b608a0`, review task
  `28109f44-31a9-46aa-83e1-e5f4ce61802f`, Reviewer 5874, commit
  `368b3cec32d30129c07825e0ce549058b99762f4`. Its
  `derivative_quotient_support` is the quotient form of BZ77 4.7(a) described above.
  Its Markdown lists its published inputs: among them the geometric lemma
  `f606bb75-3194-405e-ba6a-1edb4294d539` and the Ze80 3.7(b) comparison
  `998f43e6-dc22-4288-98b7-7343dd9ebc1c`. It also gives its own independence audit.
  At integration, its two whole-Levi cuspidality transport lemmas were replaced by an
  import of the shared module `CuspidalSupport.WholeLeviTransport`. That module holds
  the same-named lemmas, with their statements and proofs, first published in
  `Exponents.PersistenceTransport` (definition `9b5a2eb3-b44a-49ff-80e6-063cd86af3fc`,
  task `7bdc80e5-04ef-4b8e-b478-7ddba140b631`).
- `Langlands.Representation.Classification.HighestDerivativeSupportShiftBoundary`
  (Worker 128): definition `24f89507-dd1d-462e-91bc-d48acf199c19`, review task
  `b58817e9-2167-41c4-ac01-605ae891da8e`, Reviewer 5817, commit
  `a9fde2164dfeae002c8c27324c18bdcd395f447d`.
  Its `highestGeneralLinearDerivativeOrder_pos` and
  `IsSupercuspidalSupport.twist_le_of_rank_zero` handle `k = 0` and `k = n`. Order
  positivity rests on the published mirabolic joint vanishing
  (`MirabolicDerivativeVanishing`). The rank-zero support inequality follows from
  `IsSupercuspidalSupport.sum_rank` and the positivity of datum ranks
  (`CuspidalDatum.rank_pos`), then `Multiset.map_zero` and `zero_le`. It uses no
  derivative result.

The Boundary pair in the audited Library base is byte-identical to the files frozen
in its accepted artifact `24f89507-dd1d-462e-91bc-d48acf199c19`. The quotient helper
pair is the published integrated version at commit
`368b3cec32d30129c07825e0ce549058b99762f4`. It differs from the files frozen in
`bf38b454-70f8-4bf4-83b2-0def96b608a0` by the shared transport extraction described
above: the Lean file imports `CuspidalSupport.WholeLeviTransport` instead of its own
copy of the two transport lemmas, and the Markdown describes that import and no longer
gives line numbers.

Task `f81d9b36-2615-4fec-abc2-50ef93d880bf` lists as a requirement the accepted and
published BZ77 4.4 proof `fd42c8ef-e65b-4942-9a76-d41f2e22bcd3`
(`SupercuspidalDerivatives`). The implemented route does not need it and does not
import it, because the quotient form of (a) is proved without the Leibniz filtration.
The proposition definitions of the target module, including the one for (a), are
never used as premises.

## Published inputs

Every theorem used below has an independently accepted and published proof, or is a
reviewed lemma inside a published `lean.definition` or `lean.proof` artifact. Rows
give the module (prefix `Langlands.Representation.`), the publication artifact, its
task, reviewer and commit, and the declarations used.

| Module | Publication | Used |
| --- | --- | --- |
| `Classification.SupercuspidalEmbeddingProof` | proof `437ea2bb-6c0f-48b7-8b8a-8bb603ea94c1`, task `7026677a-4d36-4131-8e68-7f3e4f8f5d44`, Reviewer 1507, commit `451f42a052568843a4d727659c3d0a6c66d38ca6` | `glSupercuspidalEmbedding` (for `ω` and for `σ`) |
| `Classification.SupercuspidalSupportUniquenessProof` | proof `9533b6b3-978a-4af6-b471-c377a9c7d9c1`, task `b0b54bc0-bcdc-4408-a949-7433faa9933d`, Reviewer 5468, commit `4c0ab0f3966f1a1836901963afb04dca21607ffb` | `glSupercuspidalSupportUniqueness` (three times) |
| `CuspidalSupport.CuspidalEmbeddingProof` | proof `b518020e-e833-4191-b440-3d28855cfaf2`, task `d1684637-cf80-4266-8850-2d68c922d008`, Reviewer 1428, commit `4ccd65d85917da26d0a67b9c48a37859533fffa9` | `CuspidalSupport.cuspidalEmbedding`, first component only (admissibility of `σ`) |
| `Classification.SupercuspidalContragredientProof` | proof `a090c713-48fb-4d61-8e46-4d6fdb5d51b6`, task `1c921aca-ebef-4c0c-8c38-63156b8e2930`, Reviewer 3791, commit `a8a83747df99f404d5efc608ad4bce37629dd9c7` | `GeneralLinear.supercuspidalContragredient` (the dual of a supercuspidal is supercuspidal) |
| `Classification.SupercuspidalContragredient` | definition `1269a9fc-bd70-4c73-950b-c864caa0d498`, task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 617, commit `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` | `supercuspidalClassContragredient`, `supercuspidalClassContragredient_involutive`, `SupercuspidalClass.contragredient_twist`, `SupercuspidalRep.contragredient`, `supercuspidalContragredientClosed` |
| `Classification.TwistedProductOrdinaryDualProof` | proof `9fa7b554-0c7d-4246-bb6a-9cd5e8aad0cf`, task `b08e9b50-f8a4-4506-9ce5-7811ae11e2aa`, Reviewer 3849, commit `a2f65909d0470e0c9b71d24975a4fb12723f855f` | `twistedProductOrdinaryDual` |
| `Classification.TwistedProductCharacterTwistProof` | proof `ed7a2cff-394a-4b5c-a46b-ffce2c3bef65`, task `c9fc6804-0810-4bdd-afd6-703678856df8`, Reviewer 2440, commit `6066ffe8da8e977f40af9c75eda35cdbe1989d74` | `twistedProductCharacterTwist` |
| `Derivative.MirabolicHighestDerivativePairingProof` | proof `f957ae76-3779-4436-bdcb-98bc63561e07`, task `a925b519-9bb9-4927-873e-ad322d41328e`, Reviewer 4988, commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | `Derivative.mirabolicHighestDerivativePairing` (BZ77 3.8). Statement `73c253bc-3209-4800-bcc4-6a357f6c66c1`, task `e254f435-4bd3-404d-9af3-85e737a8d876`, Reviewer 4378, commit `84ad0affe3e3e8feae73b57da624fc1f16a6923b` |
| `Smooth.Contragredient.ExactProof` | proof `ed74312b-8337-47ed-a498-dfd50dcc5a6c`, task `41755c34-9780-45df-88a4-3a7ccd32727e`, Reviewer 415, commit `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` | `contragredientMap_surjective_of_injective_of_compact_cofinal` |
| `Smooth.Contragredient.AdmissibleDualityProof` | proof `81c91e2f-1a4d-45f0-98f2-0710f820d150`, task `a7dd454e-3648-46fd-99db-2029b21d38bb`, Reviewer 420, commit `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` | `smoothBidual_injective_of_compact_cofinal` |
| `CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` | proof `c862f739-656d-4705-89a9-0db3bfc7d716`, task `e1237fc1-de75-4a4d-924b-d509dc475361`, Reviewer 1360, commit `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302` | `CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible` (an irreducible representation has a nonzero vector) |
| `Category.Contragredient` | definition `ea215466-b640-4254-8915-bded05fc574b`, task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 560, commit `7c81d0a237386f36202562546586b28c306f0121` | `SmoothRep.contragredient`, `SmoothRep.isIrreducible_contragredient_iff`, `GeneralLinear.compactOpen_cofinal` |
| `Filtration.InvariantBilinear` | definition `45614bc5-3bfe-4a3f-b9c6-9d8229556ac9`, task `61e4dc9c-f1c3-4819-852e-211a1d6b0ccd`, Reviewer 2457, commit `efd2d4ad29b604323d377709077ba4b253e1c0f8` | `InvariantBilinear.forms` |
| `Induction.BlockEquivalence` | definition `f9b2bd9b-6179-4db9-8a7f-1d8169475c5d`, task `9ca9174f-3d3d-49ab-8341-916373cf5659`, Reviewer 1862, commit `39cbb4efb23ddd4f60b5e4f4663b2cf82258e2bf` | `normalizedProductInducedEquiv` |
| `Induction.BlockFactors` | definition `ee7ae365-79ad-4e50-8af9-25b3fa025088`, task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 174, commit `f8488ce760fd0ec518e405f24e33da3f8aaf7ef2` | `normalizedProductInductionFunctor` |
| `Classification.LanglandsData` | definition `e6099450-0e93-483c-ad05-c106c269fa72`, task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 353, commit `7465248e53e542902394c4c99a735557141755c3` | `twistedProductInduced` |
| `Classification.SupercuspidalSupport` | definitions `5f04f9a1-f335-43e2-a9da-bb6850b4b838` (task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 447, commit `a175d25f6a5a9e22525012e3cae66e9f8dfacba9`) and `6ee5d0b4-3f01-47de-94f4-06d2d3de92ce` (task `243040f2-ce4e-44b3-b3b0-11b9ac33e3f7`, Reviewer 4668, commit `6a6c913c7339c50634dd74722034032e7a167d97`) | `cuspidalProductInduced`, `cuspidalShape`, `IsCuspidalConstituent`, `IsCuspidalSubrepresentation`, `IsSupercuspidalSupport`, `SmoothRep.IsQuotient.isSubquotient` |
| `Classification.SupercuspidalTwist` | definition `cba40ce7-204a-4953-8c57-740744d48736`, task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 137, commit `6700bb7581ced62a8982c39bcea021acff83aad7` | `SupercuspidalRep.twist`, `determinantPowerCharacter`, `supercuspidalClassRealPowerTwist` |
| `Classification.Segments` | definition `556c1561-c6a2-4ce7-9791-1b99eb6fc9dc`, task `a7a453ca-879b-4dd7-a07e-bfe49c8e791c`, Reviewer 285, commit `18fac9a1ce0cc1ae5ed2c754ff093194569c18e3` | `CuspidalDatum`, `CuspidalDatum.twist`, `twist_zero`, `twist_twist`, `IsRepresentedBy`, `segmentFactor`, `SupercuspidalClass.twist_congr`. No segment, head or socle result |
| `Derivative.Iteration` | definition `13695739-0adc-4683-906f-57a8029b2353`, task `d3e94f0f-56d3-4a0f-ac7d-473214ea8038`, Reviewer 4090, commit `355c05239d7704a3ed5d72bad864cb1d542b647a` | `generalLinearDerivative`, `generalLinearRestriction`, `generalLinearRankCast`, `rank_eq_of_succ_le` |
| `Derivative.Homogeneity` | definition `609028d8-d915-4c8c-8223-2ece7bff15ff`, task `dfae49d8-a789-4eda-8ed0-f790390789b4`, Reviewer 4169, commit `c76b7751d5e9d82df7a4e5d57684adcee5d41cb7` | `mirabolicDerivativeOfOrder`, `mirabolicRankCast` |
| `Category.Twist` | definition `af4a3fca-00dc-423c-8c1c-61294d2744e5`, task `7d14a606-bb49-4cf0-9f89-8034e21e9f15`, Reviewer 274, commit `18fac9a1ce0cc1ae5ed2c754ff093194569c18e3` | `equivOfRepresentationEq` |
| `Smooth.Contragredient.Definitions`, `Smooth.Contragredient.LawsProof`, `Classification.Supercuspidal`, `Classification.ConstituentRelations`, `Category.Basic`, `Category.Subquotients`, `Twist.RealPower`, `Twist.Definitions` | current versions in definition `0a5d67d6-d44a-4544-b839-0257d12531bf`, task `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`, Reviewer 23, commit `6473a6d8b91ebfaf6d7cedffc41570c3e9edaa27` | `smoothContragredient`, `smoothDualPairing`, `contragredientMap`, `isSmooth_smoothContragredient`, `SupercuspidalRep`, `IsIrreducibleSubrepresentation`, `SmoothRep.equivOfIso`, `twist`, `twistEquiv`, `realPowerCharacter_zero`, `realPowerCharacter_neg`, `coe_realPowerCharacter`, `isOpen_ker_realPowerCharacter` |
| `Classification.SegmentSocleDerivativesStatement` | statement `c27c6879-9906-43fa-8d88-cf1808b55f2d`, task `8e5b4563-0365-41c7-b134-70f2a0b36292`, Reviewer 4178 | only the definition of the target proposition |

The group-level names `normalizedAbsUnits`, `generalLinearTopologicalGroup` and
`SmoothCharacter` come from the elementary modules `Group.GL.NormalizedCharacter`,
`Group.GL.Padic` and `Induction.Definitions`. The identity `twist 1 ρ = ρ`
(`twist_one`) comes from the published `Twist.AlgebraProof`. All of these modules
are in the audited closure below.

## Import closure audit

The direct imports are:

- the target statement module;
- the two helper pairs;
- `Classification.SupercuspidalEmbeddingProof`;
- `Classification.SupercuspidalSupportUniquenessProof`;
- `Classification.SupercuspidalContragredient` and its proof module;
- `Classification.TwistedProductOrdinaryDualProof`;
- `Classification.TwistedProductCharacterTwistProof`;
- `Derivative.MirabolicHighestDerivativePairingProof`;
- `Smooth.Contragredient.ExactProof`.

The audit was made at Library base `368b3cec32d30129c07825e0ce549058b99762f4`, which
contains both published helper pairs. It was repeated at the later base
`5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`: the closure is the same, every module in
it is byte-identical to its version at `368b3cec`, and the counts below are unchanged.
After this proof was published at commit
`8bffffb6e1e30ef5b726720a880dc9509ef3b320`, the closure was computed again there. It
is the same 626 modules, and every module other than this one is byte-identical to its
version at `5e4a58e8`. At that integration a local copy of the nonzero-vector lemma
was replaced by the published
`CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible`. Its module
`CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` was already in the non-target
closure, so the closure and the counts below do not change.

The recursive project import closure of this module has 626 modules, this module
included. It splits into two parts.

**Non-target closure (612 modules).** These are the modules reached from the ten
imports other than the target statement module. 603 of them are published by
artifacts with an owning task, among them the two helper pairs (owned by this task).
The other nine modules carry no task owner. They are integrator extractions of
elementary infrastructure: `Group.GL.OneBlockShape`, `Group.GL.Transvection`,
`HarmonicAnalysis.FiniteProductMeasureScaling`, `HarmonicAnalysis.PadicLatticeTopology`,
`Representation.Compact.OrbitMeanTranslation`, `Representation.CuspidalSupport.WholeLeviTransport`,
`Representation.OrbitSpan`, `Representation.Smooth.Transfer.GroupEquivalence` and
`Topology.CompactNormCharacter`. `WholeLeviTransport` only holds the two lemmas taken
from `Exponents.PersistenceTransport`, whose owning task `7bdc80e5` is not excluded and
has no contract requirements. `Exponents.PersistenceTransport` itself is not in the
closure.

Every published module was mapped to the artifacts that introduce or bundle it, and
each artifact to its owning task: the record's task, or for a publication the host
task of its review task. This gives 702 owning tasks. Following every contract
requirement of those tasks transitively gives 705 tasks. None of them is one of the
33 task IDs excluded by this contract. A scan of all 612 Lean files for the 21
excluded declaration names and the 33 excluded task IDs found no Lean hit. The only
Markdown hits are independence disclaimers, in the Boundary helper and in twelve
`Derivative` and `Jacquet` modules: `Iteration`, `MirabolicDerivativeVanishing`,
`MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`,
`MirabolicMinus`, `PartialDerivativeJacquetComparisonStatement`,
`PartialDerivativeJacquetLHS`, `PartialDerivativeJacquetNormalization`,
`PartialDerivativeJacquetRHS`, `PartialLocalizationData`, `TopLocalizationData` and
`Jacquet.LocalizationTower`.

**Target-only modules (13 modules).** These enter only through the mandated target
statement module `SegmentSocleDerivativesStatement`, which the contract forbids
changing:

- `Group.GL.AdjacentMergeShape`;
- `Induction.SingleBlock`;
- the `Classification` modules `MultisegmentClassificationStatement`,
  `OrderedMultisegmentHeadReduction`, `OrderedSegmentSquareIntegrableConversionStatement`,
  `RegularLanglandsStatement`, `SegmentProductPermutation`, `SegmentSocleDerivativesStatement`,
  `SegmentSocleProductData`, `SingletonSegmentSocle`, `SupercuspidalDerivativesStatement`,
  `TemperedBlockStatement` and `TrivialGroupQuotient`.

Five of these modules were introduced by `lean.definition` artifacts whose owning
tasks are on the exclusion lists:

- `TrivialGroupQuotient`: `1e56ed7e`, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
- `SegmentProductPermutation`: `0095a4c4`, task `8252833d-c269-41a9-824c-5879e531b23b`.
  This module is also bundled in proof `b61f2ca8`;
- `OrderedMultisegmentHeadReduction`: `6529dc85`, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
- `SegmentSocleProductData`: `29cea4fd`, task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`;
- `SingletonSegmentSocle`: `8aac8ad9`, task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`.

They are reached through the chain target statement ← `SingletonSegmentSocle` ←
`SegmentSocleProductData` ← the others. They supply the datum and segment-product
definitions in which the target module states its six propositions. The only
excluded names among the Lean files of these 13 modules are proposition definitions
in `MultisegmentClassificationStatement`.

The proof term does not depend on any of the 13. As an independence check, a draft
copy of this module was compiled without the target import. It proves a verbatim
copy of the target proposition with the identical proof, and it compiles with
0 errors and only the standard axioms.

## Condition-by-condition exclusion audit

Two checks support the table. The mathematical proof chain above (this module, the
two helpers and the published inputs listed) uses none of the excluded results. The
import closure audit above confirms this at the level of modules, owning tasks,
transitive requirements and identifiers. An identifier scan alone cannot exclude a
renamed result, so each row also records the mathematical inspection. Task IDs only
identify the prohibitions.

| Excluded conclusion or task family | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Not imported and not used. The proof concerns arbitrary cuspidal products, not segment products. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`; `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and successors | Not used. No linked or juxtaposed pair structure or quotient result appears. |
| `SegmentSocleProductIrreducibility`; `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Not used. No socle product criterion is applied. |
| `AdjacentUnlinkedSegmentSocleSwap`; `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | Not used. No adjacent commutation or swap appears. |
| `TwoSegmentSocleCommutation`; `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | Not used. |
| `LinkedSegmentSocleGluing`; `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Not used. |
| `OrderedMultisegmentSocleExistence`; `23189526-80b0-4828-a6d4-7ebec2cbeef5` | Not used. No ordered socle construction or existence appears. |
| `MultisegmentSocleExhaustion`, socle exhaustion; `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Not used. Its definition artifacts `SegmentSocleProductData` and `SingletonSegmentSocle` are imported only by the target statement module. The proof does not depend on them, as the draft compiled without the target import shows. No exhaustion statement or proof is imported. |
| Analytic segment classification; `aca8805b-054f-4d56-8045-12db7f623404` | Not used. No analytic or segment classification result appears. |
| Special-head multisegment exhaustion; `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Not used. |
| Ordered special/strong-head existence; `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Not used. Its definition artifact `OrderedMultisegmentHeadReduction` is imported only by the target statement module. The proof does not depend on it. |
| Quotient coverage; `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Not used. Its definition artifact `TrivialGroupQuotient` is imported only by the target statement module. The proof does not depend on it. |
| Ordered conversion; `8252833d-c269-41a9-824c-5879e531b23b` | Not used. `SegmentProductPermutation` is imported only by the target statement module. The proof does not depend on it. No multisegment conversion or permutation theorem is applied. |
| Tempered block uniqueness; `52e97845-36bb-457d-b76f-70753334b88c` | Not used. |
| `GenericSegmentProductUniqueness`; `30341ae4-65f2-4a0e-9283-763db01a409e` | Not used. |
| `SquareIntegrableLanglandsClassification`; `1cb45da2-7007-4351-a694-594fb148b8d1` | Not used. |
| Square-integrable exhaustion; `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | Not used. |
| Regular exhaustion; `bf433f0a-921a-428c-b0c0-6475438125ac` | Not used. |
| `SegmentSpecialEssentialSquareIntegrability`, forward special-segment essential square-integrability; `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Not used. No square-integrability result appears. |
| `SegmentHeadProductIrreducibility`, special-head criterion; `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Not used, and none of its conclusions appear. |
| Individual special-head/reverse-socle existence; `67279e36-f3c2-42e3-9302-11729784042e` | Not used. `Segments` is used only for the datum, its twist and `segmentFactor`. |
| Individual segment-socle/reverse-head existence; `4ca79bbd-589e-476b-9f65-661e799984b5` | Not used. |
| `SegmentFullJacquetFormula`; `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor | Not used. The only Jacquet input, inside the helper, is the general geometric lemma for the source shape together with Ze80 3.7(b). |
| `SegmentHeadJacquetFormula`; `55ad1e10-62d8-46b7-a081-909ef0056426` | Not used. |
| `SegmentSocleJacquetFormula`; `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | Not used. |
| `SegmentSpecialJacquetExponentNormFormula`; `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Not used. |
| `TwoSupercuspidalNonadjacentProductIrreducible`; `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | Not used. No two-supercuspidal irreducibility result appears. |
| `TwoSupercuspidalProductStructure`; `ab61f565-1427-4746-ba77-46097563e962` | Not used. No product structure, composition-series or two-factor Jacquet conclusion appears. |
| Parent clauses (b), (d), (e), (f) and every segment derivative formula (Ze80 §3.5, §9.6) | Not used. The derivative inputs are general: the definitions, BZ77 3.8, mirabolic joint vanishing (Boundary) and the Ze80 3.7(b) comparison (helper). The target module's proposition definitions are never premises. |
| Every segment-socle/head existence or Jacquet formula, and segment classification | Not used. See the rows above. |
| Ze80 product criteria 4.2 and 9.7, the analytic/square-integrability result 9.3, classification and exhaustion theorems | Not used. In particular the linked-pair converse of Ze80 4.2 does not enter. |
| Unproved derivative statements, citations, conditional assemblies or pending tasks | None is used. BZ77 3.8, the Ze80 3.7(b) comparison, mirabolic vanishing, the supercuspidal embedding and uniqueness, and contragredient exactness all have independently accepted and published proofs. The two helper pairs are proved in full and were independently reviewed and published before this candidate. Worker 357's minus/GL exactness and Leibniz filtration (BZ77 4.5/4.6) are not used, and nothing they own is duplicated. |

All rows exclude mathematical conclusions, proof successors and transitive dependents,
including renamed versions. No new prerequisite task was published for this proof.

## Appendix: import closure

The 612 non-target modules, grouped by namespace (`Langlands.` prefix shown in each
group heading; the count is in parentheses):

```text
Langlands.Algebra (8): CommutingDimensionHelpers, CommutingDimensionNilpotent,
    CommutingDimensionNumerics, CommutingDimensionPrimary, CommutingDimensionRecurrence,
    SandwichDimensionBoundProof, SandwichDimensionBoundStatement, SeparatedMatrixRepresentations
Langlands.Analysis.Local (18): CompactOpenCoverUnimodularityProof,
    CompactOpenCoverUnimodularityStatement, ModularCompactAverage, QuotientAutomorphismProof,
    QuotientAutomorphismStatement, QuotientAverageReal, QuotientAveragingKernel,
    QuotientComplex, QuotientFunctional, QuotientMass, QuotientMeasure,
    QuotientMeasureExistence, QuotientMeasureExistenceStatement, QuotientMeasurePrerequisites,
    QuotientPositiveLifting, QuotientTopology, QuotientTranslation, SplitKernelQuotient
Langlands.Group.GL (52): Basic, BlockContractionProof, BlockContractionStatement,
    BlockIwahoriBasis, BlockIwahoriBasisStatement, BlockIwahoriDefinitions, BlockModulus,
    BlockModulusHaarProof, BlockModulusHaarStatement, BlockUnipotentCoordinates,
    BlockUnipotentHaarProof, BlockUnipotentHaarStatement, Blocks, CartanProof, CartanStatement,
    CompactOpen, CountabilityProof, CountabilityStatement, DominantExponentGeneration,
    IntegralSubgroup, InverseTransposeIwahoriProof, InverseTransposeIwahoriStatement, Maps,
    Mirabolic, MirabolicProjection, MirabolicRadical, Nonarchimedean, NonarchimedeanStatement,
    NormalizedCharacter, OneBlockShape, OppositeBlocks, Padic, PadicBlocks, PadicOppositeBlocks,
    PadicUpperUnipotent, ParabolicModularCharacter, PrincipalBlockFactorizationProof,
    PrincipalBlockFactorizationStatement, PrincipalLevelDominance, RankMaps,
    RefinementCoordinates, ReverseBlocks, SingleBlock, SingletonBlocks, Transvection,
    TriangularParabolic, UpperBruhatEmbedding, UpperBruhatPivotProof, UpperBruhatPivotStatement,
    UpperBruhatProof, UpperBruhatStatement, UpperUnipotent
Langlands.Group (1): HaarModulus
Langlands.HarmonicAnalysis (16): AlgebraicIntegral, AlgebraicIntegrand, Basic,
    CharacterTransport, Conductor, FiniteProductMeasureScaling, PadicAdditiveConductorProof,
    PadicHaarScalingStatement, PadicLatticeTopology, PadicRectangularHaarScalingProof,
    PadicScalarHaarScalingProof, RowSchwartzAction, RowTestSmoothProof, RowTestSmoothStatement,
    TriangularTranslationProof, TriangularTranslationStatement
Langlands.LocalFactor (1): Euler
Langlands.LocalFactor.Euler (1): Definitions
Langlands.LocalFactor.Harmonic (1): Statement
Langlands.LocalField (3): Canonical, Definitions, Topology
Langlands.LocalField.Normalization (3): Definitions, Proof, Statement
Langlands.Representation.Category (5): Basic, ClassInvariants, Contragredient, Subquotients,
    Twist
Langlands.Representation.Classification (23): ConstituentCompatibility, ConstituentRelations,
    CuspidalJacquetMultiplicityStatement, CuspidalProductDerivativeQuotientSupport, Essential,
    HighestDerivativeSupportShiftBoundary, LanglandsData, Segments, Supercuspidal,
    SupercuspidalContragredient, SupercuspidalContragredientAux,
    SupercuspidalContragredientProof, SupercuspidalContragredientStatement,
    SupercuspidalEmbeddingProof, SupercuspidalEmbeddingTransport, SupercuspidalSupport,
    SupercuspidalSupportStatement, SupercuspidalSupportUniquenessProof, SupercuspidalTwist,
    Tempered, TwistedProductCharacterTwistProof, TwistedProductOrdinaryDualProof,
    UnitaryGenericCompatibilityStatement
Langlands.Representation.Compact (7): Definitions, FiniteMean, OrbitMeanTranslation,
    ProjectionProof, ProjectionStatement, SurjectivityProof, SurjectivityStatement
Langlands.Representation.CompactCoefficient (17): AdmissibleComplement, AdmissibleLifting,
    AdmissibleRetraction, AmbientProjector, Classes, ConditionalProjection,
    FixedLevelFiniteness, FixedVectorsFiniteDimensional, GroupTransport, Isotypic,
    IsotypicTransport, NormalSubgroupDecomposition, OrthogonalProjectorFamily,
    SemisimplicityProof, SemisimplicityStatement, TotalCompactness, TotalProjector
Langlands.Representation.Conductor (5): Congruence, Definitions, PrincipalCongruence,
    PrincipalCongruenceBasisProof, PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport (78): AssociatedAssembly, AssociatedConditional,
    AssociatedGeometricPieceVanishingProof, AssociatedGeometricPiecesEquivalenceProof,
    AssociatedGeometricPiecesProof, AssociatedGeometricPiecesStatement, AssociatedProof,
    AssociatedRankZero, AssociationForwardStatement, AssociationLawsProof,
    AssociationLawsStatement, AssociationReduction, AssociationReverseProof,
    AssociationReverseStatement, BlockMap, BlockPermutation, CompactCoefficientFinitenessProof,
    CompactCoefficientFinitenessReduction, CompactCoefficientFinitenessStatement,
    CuspidalEmbeddingProof, CuspidalTensorAssociationProof, CuspidalTensorProof,
    CuspidalTensorStatement, CuspidalityComparisonProof, CuspidalityComparisonStatement,
    DeterminantUnit, DeterminantUnitCartanSupport, DeterminantUnitCornerStructureProof,
    DeterminantUnitCornerStructureStatement, DualAveraging, FiltrationQuasicuspidality,
    GroupTransport, HarishChandraAssembly, HarishChandraBoundaryProof,
    HarishChandraBoundaryStatement, HarishChandraConverseProof, HarishChandraConverseStatement,
    HarishChandraForwardProof, HarishChandraStatement, JacquetInductionStatement,
    JacquetSubquotientProof, JacquetSubquotientStatement, JacquetVanishingHelpers,
    JacquetVanishingSmoothPieces, JacquetVanishingSubgroups, LeviAdmissibleFactorizationProof,
    LeviAdmissibleFactorizationStatement, LeviAssociation, LeviCompactPart,
    LeviDecompositionAssembly, LeviDefinitions, LeviGapVanishing,
    LeviQuasicuspidalDecompositionProof, LeviSplitContraction, LeviTensorFactorizationProof,
    LeviTensorFactorizationStatement, LeviTensorReflectionProof, LeviTensorReflectionStatement,
    MinimalConjugatingCosetsProof, MinimalJacquetProof, MinimalJacquetStatement,
    MinimalWeylTransportProof, NaturalProjectorDecomposition,
    NonassociatedJacquetSubquotientsProof, NormalizedCuspidalInductionStatement,
    PointwiseProjectorSum, ProperInductionMaps, ProperInductionProof, ProperInductionStatement,
    QuasicuspidalEmbeddingProof, QuasicuspidalLeviAdmissibilityProof,
    QuasicuspidalPrerequisitesStatement, QuasicuspidalStructureStatement,
    StandardJacquetComparisonProof, TotalConjugatingCountProof, TotalConjugatingCountStatement,
    WholeLeviTransport, ZeroRankEmbeddingProof
Langlands.Representation.Derivative (24): Homogeneity, Iteration, MinusVanishing,
    MirabolicCharacter, MirabolicDerivativeDetectionStatement, MirabolicDerivativeVanishing,
    MirabolicHighestDerivativeDescent, MirabolicHighestDerivativePairingProof,
    MirabolicHighestDerivativePairingStatement, MirabolicLatticeBox, MirabolicMinus,
    MirabolicMinusPairingTransferProof, MirabolicMinusPairingTransferStatement,
    MirabolicPhiMinusNondegeneratePairing, Partial, PartialDerivativeJacquetComparisonProof,
    PartialDerivativeJacquetComparisonStatement, PartialDerivativeJacquetLHS,
    PartialDerivativeJacquetNormalization, PartialDerivativeJacquetRHS,
    PartialDerivativeJacquetRHSComparison, PartialLocalizationCharacter,
    PartialLocalizationData, TopLocalizationData
Langlands.Representation.Dual (1): Definitions
Langlands.Representation.Filtration (23): CoinvariantVanishingStatement,
    CommonSubquotientStatement, Definitions, InvariantBilinear, InvariantBilinearBounds,
    IsoTransport, LengthCriterionProof, LengthCriterionStatement, MultiplicityStatement,
    NonzeroHomCommonSubquotientProof, NonzeroHomCommonSubquotientStatement, ObjectDefinitions,
    QuasicuspidalVanishingProof, QuotientFirstIso, SimpleSubquotientFactorProof,
    SimpleSubquotientFactorStatement, SubquotientAlgebraProof, SubquotientAlgebraStatement,
    SubsingletonProof, Transport, VanishingStatement, ZeroFactorDeletionProof,
    ZeroFactorDeletionStatement
Langlands.Representation.Geometric (72): BlockIntersectionSplitting, BlockSixDecomposableProof,
    BlockSixDecomposableStatement, BruhatDescent, BruhatMatrixExistenceProof,
    BruhatMatrixStatement, BruhatWeylReflectionProof, ClosedSubgroupAssembly,
    ClosedSubgroupDefinitions, ClosedSubgroupMackeyProof, ClosedSubgroupStatement,
    CompactOrbitRestriction, CompactSmoothComparison, ConditionalAssembly,
    CorrectionSubgroupCoordinates, CorrectionSubgroupDiagonalHaarProof,
    CorrectionSubgroupDiagonalHaarStatement, CosetAction, CosetOrbitHomeomorph,
    CosetOrbitOrdering, FlattenedLevi, GeneralCorrectionCharacters,
    GeneralIntersectionNormalizers, GeneralIntersections, GeometricLemmaProof,
    GeometricLemmaStatement, IntersectionLeviDiagonalCharacterProof,
    IntersectionLeviDiagonalCharacterStatement, IntersectionLeviModulusBalance,
    IntersectionTransport, MonotoneBlocksProof, MonotoneBlocksStatement, OrbitRepresentatives,
    OrbitRestriction, OrbitSectionExtensionProof, OrbitSectionExtensionStatement,
    PadicCorrectionCancellationProof, PadicCorrectionCancellationStatement,
    PadicParabolicBruhatProof, ParabolicOrbitCoefficientComparison,
    ParabolicOrbitCompactComparison, ParabolicOrbitComparisonData, ParabolicOrbitHaarComparison,
    ParabolicOrbitHaarRatio, ParabolicOrbitHaarTransport, ParabolicOrbitInductionTransport,
    ParabolicOrbitJacquet, ParabolicOrbitJacquetProof, ParabolicOrbitJacquetStatement,
    ParabolicOrbitMeasureData, ParabolicOrbitNestedAction, ParabolicOrbitNormalization,
    ParabolicOrbitNormalizedCoefficient, ParabolicOrbitSectionComparison,
    ParabolicOrbitStagesCoefficient, ParabolicSupportFiltration, ParabolicSupportGradedProof,
    ParabolicSupportGradedStatement, ParabolicSupportJacquetProof,
    ParabolicSupportJacquetStatement, ParabolicSupportTransport, RefinedPositiveCharacter,
    RefinementDefinitions, RefinementFunctors, RefinementUniqueness, SmoothSupportFiltration,
    StandardIntersectionsProof, WeylDefinitions, WeylMinimalRepresentativeProof, WeylStatement,
    WeylUniquenessProof, WeylUniquenessStatement
Langlands.Representation.Hecke (13): ActionIntegrand, ActionProjection, CommonInvarianceProof,
    CommonInvarianceStatement, Convolution, Corner, CornerAction, DoubleCoset,
    DoubleCosetSandwich, IntegratedAction, IntegratedConvolution, NormalizedIndicator,
    TestFunction
Langlands.Representation.Induction (52): BlockCharacterAbsorption, BlockEquivalence,
    BlockFactors, CharacterTwistProof, CompactAutomorphism, CompactAutomorphismIntegralProof,
    CompactAutomorphismIntegralStatement, CompactBilinearPairing,
    CompactCoinvariantBijectivityProof, CompactCoinvariantBijectivityStatement,
    CompactCoinvariantIntegral, CompactCoinvariantLocalInverseProof,
    CompactCoinvariantLocalInverseStatement, CompactLocalSection,
    CompactLocalSectionSpanningProof, CompactLocalSectionSpanningStatement,
    CompactLocallyConstant, CompactPairingDuality, CompactQuotientCutoff, CompactQuotientProof,
    CompactScalarProof, CompactScalarStatement, CompactSurjectivityProof,
    CompactSurjectivityStatement, CompactTransitivityProof, CompactTransitivityStatement,
    Definitions, Equivalences, FiniteProductTensor, FiniteProductTensorBijectiveProof,
    FiniteProductTensorBijectiveStatement, InverseTranspose, NormalCoinvariantKernelProof,
    NormalCoinvariantKernelStatement, NormalCoinvariantMap, NormalCoinvariantProof,
    NormalCoinvariantStatement, NormalSplitComparison, OppositeParabolic, Parabolic,
    PiScalarIntegral, SplitKernelCompact, SplitKernelCovariance, SplitKernelEquivariant,
    SplitKernelIntegral, SplitQuotientProof, SplitQuotientStatement, SplitStagesComparison,
    SplitStagesRetraction, StructuralStatement, SurjectivityProof, SurjectivityStatement
Langlands.Representation.Jacquet (36): BlockCompressionProof, BlockCompressionStatement,
    BlockPowerKernelProof, CanonicalLiftBijectivityProof, CanonicalLiftDefinitions,
    CanonicalLiftGroupTransportProof, CanonicalLiftGroupTransportStatement,
    CanonicalLiftIntertwinerNaturalityProof, CanonicalLiftIntertwinerNaturalityStatement,
    CanonicalLiftStatement, CharacterAveraging, CharacterTwistEquiv, Coinvariants,
    CompactCompressionStableDualityProof, CompactCompressionStableDualityStatement,
    CompressionStabilizationProof, CompressionStabilizationStatement, ExactProof,
    ExactStatement, Localization, LocalizationTower, LocalizationTransport, Normalized,
    OppositeCanonicalLiftProof, OppositeCanonicalLiftStatement, Parabolic, PositiveCharacter,
    RefinedOppositeCanonicalLiftProof, RefinedOppositeCanonicalLiftStatement,
    RefinedOppositeCompressionProof, RefinedOppositeCompressionStatement,
    RefinedOppositePowerKernelProof, RefinedOppositeStableImageProof,
    RefinedUpperCanonicalLiftProof, SmoothTwist, StablePairingProof
Langlands.Representation.MatrixCoefficient (4): Definitions, LawsProof, LawsStatement,
    ModuloCenter
Langlands.Representation (2): OrbitSpan, SubrepresentationLattice
Langlands.Representation.Parabolic (26): AdmissibilityStatement,
    GeometricPrerequisitesStatement, LeviBridges, LeviInflationAdmissibilityProof,
    NaturalInductionDualityFromScalar, NaturalInductionDualityProof,
    NaturalInductionDualityStatement, NaturalJacquetDualityProof,
    NaturalJacquetDualityStatement, NormalizedAdmissibilityProof,
    NormalizedCompatibilityStatement, NormalizedInductionStatement,
    NormalizedJacquetExactnessProof, NormalizedJacquetStatement, OppositeRefinementDefinitions,
    OppositeRefinementFunctors, QuotientCompactProof, RefinedInductionAdmissibility,
    RefinedInductionTensorMap, RefinedInductionTensorNormalization, RefinedInductionTensorProof,
    RefinedInductionTensorStatement, RefinementCharacter, RefinementComposition,
    RefinementPreimage, UnipotentFiniteContainment
Langlands.Representation.RankinSelberg (21): AnalyticStatement, EqualRankFrobeniusProof,
    EqualRankFrobeniusStatement, EqualRankTrilinearAssembly, EqualRankTrilinearReduction,
    EqualRankTrilinearUniquenessStatement, GeneralLinearUnimodularity, LastRowCompactOrbitProof,
    LastRowCompactOrbitStatement, LocalFactor, Measures, QuotientIntegrals, RankOneQuotient,
    RationalContinuation, RationalZeta, TwistInvariance, UnimodularityStatement,
    UnipotentQuotient, UnipotentUnimodularity, ZeroRowLastRowCutoffProof,
    ZeroRowLastRowCutoffStatement
Langlands.Representation.Schur (2): CountableDimensionProof, CountableDimensionStatement
Langlands.Representation.Shahidi (1): TwoBlocks
Langlands.Representation.Smooth.Admissibility (6): CofinalProof, CofinalStatement,
    EmbeddingProof, EmbeddingStatement, EquivalenceProof, EquivalenceStatement
Langlands.Representation.Smooth.Contragredient (14): AdmissibleDualityProof,
    AdmissibleDualityStatement, CompactDualityProof, CompactDualityStatement, Definitions,
    ExactProof, ExactStatement, FixedVectorsDefinitions, HomDualityProof, HomDualityStatement,
    InvariantPairingProof, InvariantPairingStatement, LawsProof, LawsStatement
Langlands.Representation.Smooth (3): Definitions, SmallRealizationProof,
    SmallRealizationStatement
Langlands.Representation.Smooth.Factorization (3): MultiplicityDefinitions,
    TwoFactorExistenceProof, TwoFactorStatement
Langlands.Representation.Smooth.FixedVectors (5): Definitions, LawsProof, LawsStatement,
    OrderProof, OrderStatement
Langlands.Representation.Smooth.Schur (2): Proof, Statement
Langlands.Representation.Smooth.SmoothPart (4): BasicProof, BasicStatement, Definitions,
    FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer (5): GroupEquivalence, PullbackProof,
    PullbackStatement, SubquotientProof, SubquotientStatement
Langlands.Representation.Tensor (12): CoinvariantReflection, Finite, FiniteEquivalences,
    FiniteProperties, FiniteRegrouping, FlattenedGLRefinement, GLRefinement, SmoothDual,
    SmoothDualInjectivityProof, SmoothDualInjectivityStatement, SmoothDualSurjectivityProof,
    SmoothDualSurjectivityStatement
Langlands.Representation.Twist (16): AdmissibilityProof, AdmissibilityStatement, AlgebraProof,
    AlgebraStatement, ContinuousCharacterProof, ContinuousCharacterStatement, Definitions,
    DualProof, DualStatement, RealPower, SmoothPartDefinitions, SmoothProof, SmoothStatement,
    SubquotientDefinitions, SubquotientProof, SubquotientStatement
Langlands.Representation.Unitary (2): Basic, Twist
Langlands.Representation.Whittaker (11): Algebraic, AlgebraicTwist, CharacterChange,
    DualTransform, EntrywiseCharacter, GeneralLinear, Iwasawa, MirabolicQuotientMeasure,
    PrerequisiteInterfaces, PrerequisitesStatement, Twist
Langlands.Topology (1): CompactNormCharacter
Langlands.Topology.CompactOpen (3): ConjugationStabilizer, NeighborhoodBasis,
    NeighborhoodBasisStatement
Langlands.Topology.GroupAction (2): FiniteOrbitProof, FiniteOrbitStatement
Langlands.Topology.Nonarchimedean (1): Subgroup
Langlands.Weil.Representation (6): Basic, Continuity, ContinuityProof, Determinant,
    IsomorphismInvarianceProof, Operations
```

The 13 target-only modules are listed in the import closure audit above. Together
with this module they complete the closure of 626 modules.
