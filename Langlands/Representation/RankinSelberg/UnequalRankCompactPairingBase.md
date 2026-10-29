# Adjacent-rank unequal-rank compact mirabolic pairings

Author: Worker 896.

Module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingBase`.
This is a helper step towards the proof of
`Langlands.RankinSelberg.UnequalRankCompactGenericPairingStatement`. It covers
the adjacent rank `r = n + 1` of the unequal-rank pairing space of JPSS (1983),
Section 2.11, which the Library defines in
`Langlands.Representation.RankinSelberg.UnequalRankBilinearForms`. The
published module `UnequalRankCompactPairingReduction` reduces every `r > n` to
this rank. This module states no new proposition.

Notation: `N = GeneralLinear.upperUnipotent (n + 1) F`, `θ = standardCharacter ψ n`,
`τ = mirabolicCompactInduced ψ (n + 1)`. `τ` is the compact model on the
mirabolic subgroup `P_(n+1)` of `GL_(n+2)`, and
`levi : GL_(n+1) → P_(n+1)`, `g ↦ diag(g, 1)`.

## Main results

```lean
abbrev GLCompactFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : Type uF :=
  Induction.CompactFunctions (GeneralLinear.upperUnipotent (n + 1) F)
    (characterRepresentation (standardCharacter ψ n))

abbrev glCompactInduced (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) (GLCompactFunctions ψ n) :=
  Induction.compactInduced (GeneralLinear.upperUnipotent (n + 1) F)
    (characterRepresentation (standardCharacter ψ n))

def leviEquiv [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [T2Space F] [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F)]
    (ψ : UnitaryAdditiveCharacter F) (hψ : IsOpen {t : F | ψ.complex t = 1}) :
    Representation.Equiv ((mirabolicCompactInduced ψ (n + 1)).comp levi)
      (glCompactInduced ψ n)

def formsAdjacentEquiv (ψ) (abv : AbsoluteValue F ℝ) (η : Representation ℂ
    (Langlands.GeneralLinear (n + 1) F) W) (hψ : IsOpen {t : F | ψ.complex t = 1})
    (hopen : Shahidi.IsOpenNormOne abv) (s : ℂ) :
    unequalRankMirabolicForms (Nat.lt_add_one n) ψ abv (mirabolicCompactInduced ψ (n + 1)) η s
      ≃ₗ[ℂ] InvariantBilinear.forms (glCompactInduced ψ n) η (fun _ => (1 : ℂ))
```

`glCompactInduced ψ n` is the compact Whittaker induction `c-Ind_N^(GL_(n+1)) θ`,
built from the published `Induction.compactInduced`. `leviEquiv` says that
restricting `τ` to `GL_(n+1)` along `levi` gives exactly `c-Ind_N^(GL_(n+1)) θ`.
The map is `f ↦ f ∘ levi`.

`formsAdjacentEquiv` describes the adjacent-rank forms of the published space
`unequalRankMirabolicForms`. For any representation `η` of `GL_(n+1)` and every
`s`, these forms are the same as the bilinear forms on
`c-Ind_N^(GL_(n+1)) θ × η` that are invariant under the diagonal action of
`GL_(n+1)`.

The hypotheses:

- `hψ` asks that the kernel of `ψ` be open. It follows from
  `MirabolicWhittaker.isOpen_complex_eq_one` on a nonarchimedean field.
- `hopen` asks that `abv` be `1` on an open subgroup of units. For the
  normalized absolute value of a p-adic field this is
  `MirabolicCompactTwistedPairing.isOpenNormOne_normalizedAbsoluteValue`.
- `η` needs no smoothness for this module.

## Construction and proofs

1. **Algebra and characters.**
   - `upperUnipotent_mulVec_last`: an upper unipotent matrix does not change the
     last coordinate of a vector.
   - `lastColumn_upperUnipotent_mul_last`: for `u` upper unipotent in `P_(n+1)`,
     the last radical coordinate of `u p` is the sum of those of `p` and `u`.
   - `mirabolicCharacter_eq_projection`: the mirabolic standard character
     factors as `ψ(last radical coordinate of u) · θ(projection u)`. This is the
     published `MirabolicWhittaker.mirabolicCharacter_succ`.
   - `mirabolicCharacter_leviUnipotent`: in particular the mirabolic character
     restricts to `θ` along `levi`.
   - Helpers: `projectionUnipotentGL` and `leviUnipotent` are `projection` and
     `levi` on the unipotent subgroups. Their memberships come from
     `MirabolicQuotient.projection_mem_upperUnipotent` and
     `MirabolicQuotient.levi_mem_upperUnipotent`.
2. **Restriction (`leviRestriction`).** The map is `f ↦ (a ↦ f(levi a))`.
   - Covariance under `N`: `mirabolicCharacter_leviUnipotent`.
   - Uniform smoothness: pull back an open subgroup of right periods along the
     continuous `levi`.
   - Compact support modulo `N`: the projected support lies in the image of the
     projected support of `f` under the published homeomorphism
     `MirabolicQuotient.quotientHomeomorph`, and the projected support is closed.
3. **Extension (`leviExtension`).** The map is
   `h ↦ (p ↦ ψ(lastColumn p last) · h(projection p))`.
   - Covariance under the mirabolic unipotent group: by step 1.
   - Smoothness (`leviExtendPeriods_mem_nhds`): this uses `hψ`. Choose a compact
     `C ⊆ GL_(n+1)` whose image is the projected support of `h`, using
     `QuotientIntegration.leftQuotient_exists_isCompact_image`. The tube lemma
     gives an open `U ∋ 0` with `ψ((c x)_last) = 1` for `c ∈ C`, `x ∈ U`. Then
     every `k` with `projection k` a period of `h` and `lastColumn k ∈ U` is a
     right period of the extension. The argument splits into two cases:
     - when `h(projection p) = 0` both sides vanish;
     - otherwise `projection p ∈ N c` with `c ∈ C`, and the extra phase
       `ψ(((projection p) x)_last) = ψ((c x)_last)` is `1`.

     The right periods form a subgroup (`leviExtendPeriods`), so this subgroup
     is open.
   - Compact support: the projected support lies in the image of that of `h`
     under the inverse quotient homeomorphism.
4. **Equivalence (`leviEquiv`).** The two maps are mutually inverse:
   - `leviExtension ∘ leviRestriction = id` is
     `eval_eq_lastColumn_mul_levi`. It follows from
     `p = radicalElement (lastColumn p) · levi (projection p)` and covariance
     under the radical, using the published `mirabolicCharacter_radicalElement`.
   - `leviRestriction ∘ leviExtension = id`: `lastColumn (levi a) = 0` and
     `projection (levi a) = a`.

   `leviRestriction` intertwines because `levi` is a homomorphism.
5. **Adjacent forms.**
   - `unequalRankEmbedding_adjacent`: the block embedding `diag(g, I_1)` is
     `levi g`. This is checked entrywise.
   - `forms_adjacent_eq`: the published group `U_(n+2,n+2)` is trivial
     (`unequalRankCovarianceSubgroup_adjacent`), so the unipotent covariance law
     is vacuous. The forms are then exactly
     `InvariantBilinear.forms (τ ∘ levi) η (g ↦ |det g|^((n+1-n)/2 - s))`.
   - `formsAdjacentEquiv` composes three steps:
     - this equality;
     - `InvariantBilinear.equivLeft` along `leviEquiv`;
     - the published `Induction.formsCharacterShift` with the character
       `Shahidi.determinantPower abv (n + 1) ((n+1-n)/2 - s)`. This character is
       trivial on `N` (`determinantPower_unipotent`, since unipotent matrices
       have determinant `1`), and its kernel is open by `hopen`.

## Provenance

The forms are those of JPSS (1983), Section 2.11, (2.11.2) and (2.11.4), and the
Lemma on p.399 (literature ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`), as published
in `UnequalRankBilinearForms`. The identification of the restricted compact
mirabolic model with `c-Ind_N^(GL_(n+1)) θ`, and the resulting description of the
adjacent-rank forms, are internal derived steps of this formalization. No claim
is made that JPSS state them in this form. All the named helpers
(`leviRestriction`, `leviExtension`, `leviExtendPeriods`, `projectionUnipotentGL`,
`leviUnipotent`, `formsAdjacentEquiv`) are derived constructions with no separate
literature counterpart.
