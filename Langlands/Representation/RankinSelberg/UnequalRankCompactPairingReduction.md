# Rank reduction for unequal-rank compact mirabolic pairings

Author: Worker 896.

Module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingReduction`.
This is a helper step towards the proof of
`Langlands.RankinSelberg.UnequalRankCompactGenericPairingStatement`. It removes
one row and column at a time from the compact mirabolic model in the
unequal-rank pairing space of JPSS (1983), Section 2.11, which the Library
defines in `Langlands.Representation.RankinSelberg.UnequalRankBilinearForms`.
It states no new proposition.

## Main result

```lean
def Langlands.RankinSelberg.UnequalRankCompactPairing.formsSuccEquiv
    {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    {n m : ℕ} [LocallyCompactSpace (Langlands.GeneralLinear (m + 1) F)]
    [LocallyCompactSpace (Langlands.GeneralLinear (m + 2) F)]
    [NonarchimedeanGroup (Langlands.GeneralLinear (m + 2) F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hnm : n < m) (hψ : IsOpen {t : F | ψ.complex t = 1}) (s : ℂ) :
    unequalRankMirabolicForms hnm ψ abv (mirabolicCompactInduced ψ m) η (s - 1 / 2) ≃ₗ[ℂ]
      unequalRankMirabolicForms (Nat.lt_add_one_of_lt hnm) ψ abv
        (mirabolicCompactInduced ψ (m + 1)) η s
```

Write `τ_m = mirabolicCompactInduced ψ m`. This is the compact model on the
mirabolic subgroup `P_m` of `GL_(m+1)`. Write `R = MirabolicWhittaker.restriction ψ`
for restriction `τ_(m+1) → τ_m` along the successor embedding
`successor : P_m → P_(m+1)`, `f ↦ (p ↦ f (successor p))`. `R` is published in
`Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness`.
For `n < m` and every representation `η` of `GL_(n+1)` (no smoothness,
admissibility or irreducibility is needed), the equivalence sends a form `B'`
to `B' ∘ R` (`formsSuccMap`, `formsSuccMap_val`). Here `B'` is covariant of rank
`m` at exponent `s - 1/2` (both laws of `IsUnequalRankMirabolicCovariant`), and
`B' ∘ R` is covariant of rank `m + 1` at exponent `s`. The exponent shift comes
from the weights: `((m + 1 - n) / 2 - s) = ((m - n) / 2 - (s - 1/2))`
(`weight_succ`).

The hypotheses on `F` and `GL` are those of the published `R` and its
surjectivity theorem `MirabolicWhittaker.restriction_surjective`. They hold for a
p-adic field with its canonical topology (compare
`Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof`).
`hψ` follows from `MirabolicWhittaker.isOpen_complex_eq_one` when `F` is a
nonarchimedean additive group.

## Proof

1. **Algebra (section `Algebra`).**
   - `unequalRankEmbedding_succ`: the block embedding
     `GL_(n+1) → P_(m+1)` is the successor of the block embedding
     `GL_(n+1) → P_m`. This is checked entrywise with `unequalRankEmbedding_entry`,
     `successor_first`, `successor_last` and `levi_bottom`.
   - The helper maps `successorUnipotent : U_(m+1) → U_(m+2)`,
     `plusUnipotent : U_(m+2) → plusSubgroup m F` and
     `projectionUnipotent : U_(m+2) → U_(m+1)` (leading `(m+1)`-block) are
     defined.
   - The lemmas `isCovarianceUnipotent_successor`,
     `isCovarianceUnipotent_projectionUnipotent` and
     `isCovarianceUnipotent_radical` say that these maps preserve JPSS's group
     `U_(n+2,·)` (leading `(n+2)`-block equal to the identity). They also say that
     every radical element `radicalElement x` of `P_(m+1)` lies in `U_(n+2,m+2)`
     when `n < m`.
2. **Characters (section `Characters`).** These are the published mirabolic-character
   identities restated for `standardCharacter`:
   - `standardCharacter_succ`: `θ_(m+1)(u) = ψ(u_(m,m+1)) θ_m(projection u)`;
   - `standardCharacter_successor`: `θ_(m+1)(successor u) = θ_m(u)`;
   - `standardCharacter_radicalElement`: `θ_(m+1)(radicalElement x) = ψ(x_last)`.
3. **Restriction (section `Restriction`).** `R` intertwines the two block
   embeddings (`restriction_unequalRankEmbedding`, from the published
   `restriction_translate`). It turns radical translation into multiplication by
   `ψ(x_last)` (`restriction_radicalElement`, from `eval_mul_radicalElement` and
   the fact that the row of a successor is the last row of `1`). For `p` in the
   plus subgroup, `R(p · f) = ψ(lastColumn p last) · (plusProjection p) · R f`
   (`restriction_plus`, via `plus_eq_radicalElement_mul_successor`).
4. **Covariance transfer (section `Forms`).** `comp_restriction_mem`: if `B'` is
   covariant of rank `m` at `s - 1/2`, then `B' ∘ R` is covariant of rank `m + 1`
   at `s`. The `GL_(n+1)` law uses steps 1 and 3. The unipotent law writes
   `u ∈ U_(n+2,m+2)` as an element of the plus subgroup and uses
   `restriction_plus` and `standardCharacter_succ`.
   `mem_of_comp_restriction_mem` is the converse when `R` is surjective. Every
   function of rank `m` is `R f`. For `u ∈ U_(n+2,m+1)` it applies the law of
   `B' ∘ R` to `successorUnipotent u` together with `standardCharacter_successor`.
5. **Kernel vanishing (sections `Kernel`, `KernelVanishing`).** Call a functional
   `ℓ` on `τ_(m+1)` radical-covariant (`IsRadicalCovariant`) if
   `ℓ(radicalElement x · f) = ψ(x_last) ℓ(f)`.
   `functional_eq_zero_of_restriction_eq_zero` shows that every such `ℓ`
   vanishes on `ker R`, provided the kernel of `ψ` is open. These are copies of
   the published `MirabolicWhittaker.functional_eq_zero_of_finset` and
   `MirabolicWhittaker.functional_eq_zero_of_restriction_eq_zero` with the same
   proofs: an induction over a finite set of radical characters, then a compact
   cover of the row set. The one change is in the hypothesis. The published
   versions assume a full Whittaker functional, but the proof uses only the
   radical covariance. Here that covariance is all that is available, because
   the unipotent law of the forms involves only `U_(n+2,m+2)`, which contains the
   radical (step 1) but not all of `U_(m+2)`.
6. **Factorization (section `Factorization`).** `exists_comp_restriction`: for
   each `w`, the functional `B(·, w)` of a covariant form `B` of rank `m + 1` is
   radical-covariant (steps 1, 2), so it vanishes on `ker R` (step 5). Hence
   `B = B' ∘ R` with
   `B' = (ker R).liftQ B ∘ (R.quotKerEquivOfSurjective _).symm`.
   - `formsSuccMap_injective`: `R` is surjective (`LinearMap.cancel_right`).
   - `formsSuccMap_surjective`: steps 4 and 6.
   - `formsSuccEquiv` is `LinearEquiv.ofBijective`.

## Provenance

The forms are those of JPSS (1983), Section 2.11, (2.11.2) and (2.11.4), and the
Lemma on p.399. The compact case of that Lemma is discussed on p.403
(literature ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). JPSS do not
state this rank reduction. It is an internal derived step. It reduces
`r = m + 1` to `r = n + 1` by successive restriction, in the same way that
`MirabolicCompactWhittakerUniqueness` reduces Whittaker uniqueness on the
compact model. The kernel-vanishing argument of step 5 is that module's argument
with a weaker hypothesis. The derived helpers `successorUnipotent`,
`plusUnipotent`, `projectionUnipotent`, `IsRadicalCovariant` and `formsSuccMap`
have no literature counterpart.
