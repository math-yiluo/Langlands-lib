# The positive support shift of an irreducible highest derivative (BZ77 4.7(b))

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
Library's normalized induction. Hence no Haar-modulus comparison is needed, and none
is used.

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

- If `k ≥ n`, then `k = n` and `σ` lives on `GL_0`. The `HighestDerivativeSupportShiftBoundary` helper's
  `IsSupercuspidalSupport.twist_le_of_rank_zero` shows that `s' = 0`, which gives the
  claim.
- Otherwise `0 < n`, and `Derivative.highestGeneralLinearDerivativeOrder_pos`
  (Boundary helper) gives `0 < k`. Write `n = N + 1`.
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

Two helper pairs written for this proof are imported by their Lean names. Each is a
separate definition module of the Library, proved in full:

- `Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport`,
  added to the Library at commit
  `368b3cec32d30129c07825e0ce549058b99762f4`. Its
  `derivative_quotient_support` is the quotient form of BZ77 4.7(a) described above.
  Its Markdown lists its published inputs: among them the geometric lemma
  (`Geometric.GeometricLemmaProof`) and the Ze80 3.7(b) comparison
  (`Derivative.PartialDerivativeJacquetComparisonProof`). It also gives its own
  independence audit. In the Library, its two whole-Levi cuspidality transport lemmas
  are replaced by an import of the shared module `CuspidalSupport.WholeLeviTransport`.
  That module holds the same-named lemmas, with their statements and proofs, first
  published in `Exponents.PersistenceTransport`.
- `Langlands.Representation.Classification.HighestDerivativeSupportShiftBoundary`,
  added to the Library at commit `a9fde2164dfeae002c8c27324c18bdcd395f447d`.
  Its `highestGeneralLinearDerivativeOrder_pos` and
  `IsSupercuspidalSupport.twist_le_of_rank_zero` handle `k = 0` and `k = n`. Order
  positivity rests on the published mirabolic joint vanishing
  (`MirabolicDerivativeVanishing`). The rank-zero support inequality follows from
  `IsSupercuspidalSupport.sum_rank` and the positivity of datum ranks
  (`CuspidalDatum.rank_pos`), then `Multiset.map_zero` and `zero_le`. It uses no
  derivative result.

The Boundary pair in the audited Library base is byte-identical to its files as first
written. The quotient helper pair is the version at commit
`368b3cec32d30129c07825e0ce549058b99762f4`. It differs from its files as first
written by the shared transport extraction described above: the Lean file imports `CuspidalSupport.WholeLeviTransport` instead of its own
copy of the two transport lemmas, and the Markdown describes that import and no longer
gives line numbers.

The Library has a proof of BZ77 4.4 (`Classification.SupercuspidalDerivativesProof`).
The implemented route does not need it and does not import it, because the quotient form of (a) is proved without the Leibniz filtration.
The proposition definitions of the target module, including the one for (a), are
never used as premises.

## Published inputs

Every theorem used below has a proof in the Library, in a proof module or as a
lemma inside a definition module. Rows give the module (prefix
`Langlands.Representation.`), the commit that added it to the Library, and the
declarations used.

| Module | Added to the Library at | Used |
| --- | --- | --- |
| `Classification.SupercuspidalEmbeddingProof` | commit `451f42a052568843a4d727659c3d0a6c66d38ca6` | `glSupercuspidalEmbedding` (for `ω` and for `σ`) |
| `Classification.SupercuspidalSupportUniquenessProof` | commit `4c0ab0f3966f1a1836901963afb04dca21607ffb` | `glSupercuspidalSupportUniqueness` (three times) |
| `CuspidalSupport.CuspidalEmbeddingProof` | commit `4ccd65d85917da26d0a67b9c48a37859533fffa9` | `CuspidalSupport.cuspidalEmbedding`, first component only (admissibility of `σ`) |
| `Classification.SupercuspidalContragredientProof` | commit `a8a83747df99f404d5efc608ad4bce37629dd9c7` | `GeneralLinear.supercuspidalContragredient` (the dual of a supercuspidal is supercuspidal) |
| `Classification.SupercuspidalContragredient` | commit `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` | `supercuspidalClassContragredient`, `supercuspidalClassContragredient_involutive`, `SupercuspidalClass.contragredient_twist`, `SupercuspidalRep.contragredient`, `supercuspidalContragredientClosed` |
| `Classification.TwistedProductOrdinaryDualProof` | commit `a2f65909d0470e0c9b71d24975a4fb12723f855f` | `twistedProductOrdinaryDual` |
| `Classification.TwistedProductCharacterTwistProof` | commit `6066ffe8da8e977f40af9c75eda35cdbe1989d74` | `twistedProductCharacterTwist` |
| `Derivative.MirabolicHighestDerivativePairingProof` | commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | `Derivative.mirabolicHighestDerivativePairing` (BZ77 3.8). Statement module `Derivative.MirabolicHighestDerivativePairingStatement`, commit `84ad0affe3e3e8feae73b57da624fc1f16a6923b` |
| `Smooth.Contragredient.ExactProof` | commit `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` | `contragredientMap_surjective_of_injective_of_compact_cofinal` |
| `Smooth.Contragredient.AdmissibleDualityProof` | commit `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` | `smoothBidual_injective_of_compact_cofinal` |
| `CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` | commit `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302` | `CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible` (an irreducible representation has a nonzero vector) |
| `Category.Contragredient` | commit `7c81d0a237386f36202562546586b28c306f0121` | `SmoothRep.contragredient`, `SmoothRep.isIrreducible_contragredient_iff`, `GeneralLinear.compactOpen_cofinal` |
| `Filtration.InvariantBilinear` | commit `efd2d4ad29b604323d377709077ba4b253e1c0f8` | `InvariantBilinear.forms` |
| `Induction.BlockEquivalence` | commit `39cbb4efb23ddd4f60b5e4f4663b2cf82258e2bf` | `normalizedProductInducedEquiv` |
| `Induction.BlockFactors` | commit `f8488ce760fd0ec518e405f24e33da3f8aaf7ef2` | `normalizedProductInductionFunctor` |
| `Classification.LanglandsData` | commit `7465248e53e542902394c4c99a735557141755c3` | `twistedProductInduced` |
| `Classification.SupercuspidalSupport` | commits `a175d25f6a5a9e22525012e3cae66e9f8dfacba9` and `6a6c913c7339c50634dd74722034032e7a167d97` | `cuspidalProductInduced`, `cuspidalShape`, `IsCuspidalConstituent`, `IsCuspidalSubrepresentation`, `IsSupercuspidalSupport`, `SmoothRep.IsQuotient.isSubquotient` |
| `Classification.SupercuspidalTwist` | commit `6700bb7581ced62a8982c39bcea021acff83aad7` | `SupercuspidalRep.twist`, `determinantPowerCharacter`, `supercuspidalClassRealPowerTwist` |
| `Classification.Segments` | commit `18fac9a1ce0cc1ae5ed2c754ff093194569c18e3` | `CuspidalDatum`, `CuspidalDatum.twist`, `twist_zero`, `twist_twist`, `IsRepresentedBy`, `segmentFactor`, `SupercuspidalClass.twist_congr`. No segment, head or socle result |
| `Derivative.Iteration` | commit `355c05239d7704a3ed5d72bad864cb1d542b647a` | `generalLinearDerivative`, `generalLinearRestriction`, `generalLinearRankCast`, `rank_eq_of_succ_le` |
| `Derivative.Homogeneity` | commit `c76b7751d5e9d82df7a4e5d57684adcee5d41cb7` | `mirabolicDerivativeOfOrder`, `mirabolicRankCast` |
| `Category.Twist` | commit `18fac9a1ce0cc1ae5ed2c754ff093194569c18e3` | `equivOfRepresentationEq` |
| `Smooth.Contragredient.Definitions`, `Smooth.Contragredient.LawsProof`, `Classification.Supercuspidal`, `Classification.ConstituentRelations`, `Category.Basic`, `Category.Subquotients`, `Twist.RealPower`, `Twist.Definitions` | current versions at commit `6473a6d8b91ebfaf6d7cedffc41570c3e9edaa27` | `smoothContragredient`, `smoothDualPairing`, `contragredientMap`, `isSmooth_smoothContragredient`, `SupercuspidalRep`, `IsIrreducibleSubrepresentation`, `SmoothRep.equivOfIso`, `twist`, `twistEquiv`, `realPowerCharacter_zero`, `realPowerCharacter_neg`, `coe_realPowerCharacter`, `isOpen_ker_realPowerCharacter` |
| `Classification.SegmentSocleDerivativesStatement` | the target statement module | only the definition of the target proposition |

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
contains both helper pairs. It was repeated at the later base
`5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`: the closure is the same, every module in
it is byte-identical to its version at `368b3cec`, and the counts below are unchanged.
After this proof was added to the Library at commit
`8bffffb6e1e30ef5b726720a880dc9509ef3b320`, the closure was computed again there. It
is the same 626 modules, and every module other than this one is byte-identical to its
version at `5e4a58e8`. At that commit a local copy of the nonzero-vector lemma
was replaced by the published
`CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible`. Its module
`CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` was already in the non-target
closure, so the closure and the counts below do not change.

The recursive project import closure of this module has 626 modules, this module
included. It splits into two parts.

**Non-target closure (612 modules).** These are the modules reached from the ten
imports other than the target statement module. Nine of them are extractions of
elementary infrastructure from other modules: `Group.GL.OneBlockShape`, `Group.GL.Transvection`,
`HarmonicAnalysis.FiniteProductMeasureScaling`, `HarmonicAnalysis.PadicLatticeTopology`,
`Representation.Compact.OrbitMeanTranslation`, `Representation.CuspidalSupport.WholeLeviTransport`,
`Representation.OrbitSpan`, `Representation.Smooth.Transfer.GroupEquivalence` and
`Topology.CompactNormCharacter`. `WholeLeviTransport` only holds the two lemmas taken
from `Exponents.PersistenceTransport`, which is not excluded.
`Exponents.PersistenceTransport` itself is not in the closure.

A scan of all 612 Lean files for the 21 excluded declaration names found no Lean
hit. The only
Markdown hits are independence disclaimers, in the Boundary helper and in twelve
`Derivative` and `Jacquet` modules: `Iteration`, `MirabolicDerivativeVanishing`,
`MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`,
`MirabolicMinus`, `PartialDerivativeJacquetComparisonStatement`,
`PartialDerivativeJacquetLHS`, `PartialDerivativeJacquetNormalization`,
`PartialDerivativeJacquetRHS`, `PartialLocalizationData`, `TopLocalizationData` and
`Jacquet.LocalizationTower`.

**Target-only modules (13 modules).** These enter only through the target statement
module `SegmentSocleDerivativesStatement`, which this proof leaves unchanged:

- `Group.GL.AdjacentMergeShape`;
- `Induction.SingleBlock`;
- the `Classification` modules `MultisegmentClassificationStatement`,
  `OrderedMultisegmentHeadReduction`, `OrderedSegmentSquareIntegrableConversionStatement`,
  `RegularLanglandsStatement`, `SegmentProductPermutation`, `SegmentSocleDerivativesStatement`,
  `SegmentSocleProductData`, `SingletonSegmentSocle`, `SupercuspidalDerivativesStatement`,
  `TemperedBlockStatement` and `TrivialGroupQuotient`.

Five of these modules were introduced as definition modules for results on the
exclusion lists:

- `TrivialGroupQuotient`: quotient coverage;
- `SegmentProductPermutation`: ordered conversion;
- `OrderedMultisegmentHeadReduction`: ordered special/strong-head existence;
- `SegmentSocleProductData`: socle exhaustion;
- `SingletonSegmentSocle`: socle exhaustion.

They are reached through the chain target statement ← `SingletonSegmentSocle` ←
`SegmentSocleProductData` ← the others. They supply the datum and segment-product
definitions in which the target module states its six propositions. The only
excluded names among the Lean files of these 13 modules are proposition definitions
in `MultisegmentClassificationStatement`.

The proof term does not depend on any of the 13. As an independence check, a copy
of this module was compiled without the target import. It proves a verbatim
copy of the target proposition with the identical proof, and it compiles with
0 errors and only the standard axioms.

## Condition-by-condition exclusion audit

Two checks support the table. The mathematical proof chain above (this module, the
two helpers and the published inputs listed) uses none of the excluded results. The
import closure audit above confirms this at the level of modules and identifiers. An
identifier scan alone cannot exclude a renamed result, so each row also records the
mathematical inspection.

| Excluded conclusion | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | Not imported and not used. The proof concerns arbitrary cuspidal products, not segment products. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` and their proofs | Not used. No linked or juxtaposed pair structure or quotient result appears. |
| `SegmentSocleProductIrreducibility` | Not used. No socle product criterion is applied. |
| `AdjacentUnlinkedSegmentSocleSwap` | Not used. No adjacent commutation or swap appears. |
| `TwoSegmentSocleCommutation` | Not used. |
| `LinkedSegmentSocleGluing` | Not used. |
| `OrderedMultisegmentSocleExistence` | Not used. No ordered socle construction or existence appears. |
| `MultisegmentSocleExhaustion`, socle exhaustion | Not used. Its definition modules `SegmentSocleProductData` and `SingletonSegmentSocle` are imported only by the target statement module. The proof does not depend on them, as the copy compiled without the target import shows. No exhaustion statement or proof is imported. |
| Analytic segment classification | Not used. No analytic or segment classification result appears. |
| Special-head multisegment exhaustion | Not used. |
| Ordered special/strong-head existence | Not used. Its definition module `OrderedMultisegmentHeadReduction` is imported only by the target statement module. The proof does not depend on it. |
| Quotient coverage | Not used. Its definition module `TrivialGroupQuotient` is imported only by the target statement module. The proof does not depend on it. |
| Ordered conversion | Not used. `SegmentProductPermutation` is imported only by the target statement module. The proof does not depend on it. No multisegment conversion or permutation theorem is applied. |
| Tempered block uniqueness | Not used. |
| `GenericSegmentProductUniqueness` | Not used. |
| `SquareIntegrableLanglandsClassification` | Not used. |
| Square-integrable exhaustion | Not used. |
| Regular exhaustion | Not used. |
| `SegmentSpecialEssentialSquareIntegrability`, forward special-segment essential square-integrability | Not used. No square-integrability result appears. |
| `SegmentHeadProductIrreducibility`, special-head criterion | Not used, and none of its conclusions appear. |
| Individual special-head/reverse-socle existence | Not used. `Segments` is used only for the datum, its twist and `segmentFactor`. |
| Individual segment-socle/reverse-head existence | Not used. |
| `SegmentFullJacquetFormula` and its exact proof | Not used. The only Jacquet input, inside the helper, is the general geometric lemma for the source shape together with Ze80 3.7(b). |
| `SegmentHeadJacquetFormula` | Not used. |
| `SegmentSocleJacquetFormula` | Not used. |
| `SegmentSpecialJacquetExponentNormFormula` | Not used. |
| `TwoSupercuspidalNonadjacentProductIrreducible` | Not used. No two-supercuspidal irreducibility result appears. |
| `TwoSupercuspidalProductStructure` | Not used. No product structure, composition-series or two-factor Jacquet conclusion appears. |
| Parent clauses (b), (d), (e), (f) and every segment derivative formula (Ze80 §3.5, §9.6) | Not used. The derivative inputs are general: the definitions, BZ77 3.8, mirabolic joint vanishing (Boundary) and the Ze80 3.7(b) comparison (helper). The target module's proposition definitions are never premises. |
| Every segment-socle/head existence or Jacquet formula, and segment classification | Not used. See the rows above. |
| Ze80 product criteria 4.2 and 9.7, the analytic/square-integrability result 9.3, classification and exhaustion theorems | Not used. In particular the linked-pair converse of Ze80 4.2 does not enter. |
| Unproved derivative statements, citations or conditional assemblies | None is used. BZ77 3.8, the Ze80 3.7(b) comparison, mirabolic vanishing, the supercuspidal embedding and uniqueness, and contragredient exactness all have proofs in the Library. The two helper pairs are proved in full. Minus/GL exactness and the Leibniz filtration (BZ77 4.5/4.6) are not used, and no part of them is duplicated here. |

All rows exclude mathematical conclusions, the files proving them and transitive dependents,
including renamed versions.

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

The generic `smoothContragredientEquiv` construction is shared through
`Smooth.Contragredient.Equivalence`. Its existing classification name is an
abbreviation for the identical construction, preserving its interface.
