# Assembly of the reduction of Popescu's theorem to a field base

This module proves the reduction step of Popescu's theorem: it suffices to treat
a field base. The source is the Stacks Project, *Smoothing ring maps*, Lemma 8.4
(tag 07F5). Four statements enter as hypotheses:

- Lemma 2.8 (`SingularIdealFactorizationStatement`, Stacks 07EU);
- nilpotent lifting (`NilpotentLiftingStatement`, Stacks Proposition 5.3);
- the strictly standard desingularization step
  (`StrictlyStandardDesingularizationStatement`), which replaces Lemmas 6.1 and
  7.2 of the source;
- Lemma 8.3 (`LocalizationStandardDescentStatement`, Stacks 07F4), in its
  strictly standard form.

The proof in Lean differs from the source in two places.

- **Fibre field.** The source localizes at all nonzerodivisors and works over the
  total ring of fractions, a finite product of fields. The Lean proof instead
  localizes at one minimal prime `p` of the reduced ring `R`. The local ring
  `R_p` is then the field `κ(p)`, and only one fibre is needed.
- **Final step.** The source concludes with Lemmas 6.1 and 7.2. The Lean proof
  uses the desingularization statement to reach a factorization `A → B₂ → Λ`
  with `H_{B₂/R} Λ = Λ`, and then applies Lemma 2.8.

## Transfer and regularity lemmas

- `hasSmoothFactorizations_of_ringEquiv'` from `ArtinianBottom`: property PT
  (`HasSmoothFactorizations`) transfers along ring isomorphisms `R₂ ≅ R₁` and
  `Λ₂ ≅ Λ₁` that commute with the structure maps. Given `f : A → Λ₂`, view `A`
  as an `R₁`-algebra and factor `A → Λ₂ ≅ Λ₁` through a smooth `R₁`-algebra `B`.
  Then `R₂ ⊗[R₁] B` is smooth over `R₂`, and `A → R₂ ⊗[R₁] B → Λ₂` factors `f`.
- `GeometricallyRegular.baseChange_of_bijective`: if `k → k'` is an isomorphism
  of fields, then geometric regularity of `A` over `k` gives geometric regularity
  of `k' ⊗[k] A` over `k'`. A finite purely inseparable extension of `k'` is one
  of `k` as well, and `Algebra.TensorProduct.cancelBaseChange` identifies the
  tensor products.
- `regularAlgebra_of_geometricallyRegular`: over a field `k`, a geometrically
  regular algebra is a regular algebra. The only prime is `⊥`, and `k → κ(⊥)` is
  an isomorphism.
- `regularAlgebra_quotient`: if `R → Λ` is regular, then so is
  `R/I → Λ/IΛ` (Stacks, More on Algebra, Lemma 42.3, in the form needed here).
  - Flatness: `Λ/IΛ ≅ (R/I) ⊗[R] Λ`, by
    `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`.
  - Fibres: for a prime `P` of `R/I` with preimage `p` in `R`, the map
    `κ(p) → κ(P)` is bijective (`RingHom.SurjectiveOnStalks.residueFieldMap_bijective`).
    The fibre of `Λ/IΛ` at `P` is isomorphic to `κ(P) ⊗[κ(p)] (κ(p) ⊗[R] Λ)`,
    via `cancelBaseChange` twice and the isomorphism above. So geometric
    regularity transfers from the fibre of `Λ` at `p`.

## Auxiliary lemmas

- `mul_eq_zero_of_sq_mul_eq_zero`: in a ring with zero nilradical,
  `π²x = 0` implies `πx = 0`, because `(πx)² = 0`.
- `flat_mul_eq_zero_of_sq_mul_eq_zero`: suppose `R` has this property for `π`
  and `Λ` is flat over `R`. Then `Λ` has it too. If `π²x = 0` in `Λ`, the
  equational criterion for flatness (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`)
  writes `x = Σ aⱼ yⱼ` with `π² aⱼ = 0`, so `π aⱼ = 0` and `πx = 0`.
- `singularIdeal_eq_top_of_smooth`: the singular ideal of a smooth algebra is the
  unit ideal, since its smooth locus is the whole spectrum.
- `mem_singularIdeal_of_smooth_away`: if `B_b` is smooth over `R` (with `B`
  finitely presented), then the basic open set of `b` lies in the smooth locus.
  So `b` lies in every prime outside the smooth locus, that is, in `H_{B/R}`.
- `isLocalization_residueField_of_mem_minimalPrimes`: if `R` is reduced and `p`
  is a minimal prime, then `κ(p)` is the localization of `R` at `p`. The maximal
  ideal of `R_p` is the radical of `0` there
  (`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`). That radical is
  zero because `R_p` is reduced. So `R_p → κ(p)` is bijective.

## Key lemma

`exists_strictlyStandard_factorization` assumes the field case and Lemma 8.3. Let
`R → Λ` be regular and `p` a prime with `κ(p)` a localization of `R` at `p`.
Then every `f : A → Λ` with `A` finitely presented factors as `A → B → Λ`, where
`B` is finitely presented and some `s ∉ p` is strictly standard in `B` over `R`.

The fibre `κ(p) ⊗[R] Λ` is Noetherian and geometrically regular over `κ(p)`. So
the field case factors `κ(p) ⊗[R] A → κ(p) ⊗[R] Λ` through a smooth
`κ(p)`-algebra `B'`. The fibre is the localization of `Λ` at the image of the
complement of `p` (`IsLocalization.tensorRight`). Lemma 8.3 then descends the
factorization.

`hasSmoothFactorizations_of_quotients` assumes all four hypotheses and the field
case. Let `R` be Noetherian and `R → Λ` regular, and suppose PT holds for
`R/J → Λ/JΛ` for every nonzero ideal `J`. Then PT holds for `R → Λ`.

1. If the nilradical is nonzero, it is a nonzero nilpotent ideal. Nilpotent
   lifting gives PT.
2. Otherwise `R` is reduced. It suffices to factor `f` through some finitely
   presented `B₂` with `H_{B₂/R} Λ = Λ`, by Lemma 2.8. If `R` is the zero ring,
   `Λ` is too and `B₂ = A` works.
3. Otherwise pick a minimal prime `p`. The previous lemma gives `A → B → Λ` with
   `s ∉ p` strictly standard in `B`. The annihilator conditions for `s` hold in
   `R` (reduced) and in `Λ` (flat). Also `s⁸ ≠ 0`, because `s` is not nilpotent.
4. PT for `R/s⁸R → Λ/s⁸Λ` factors `(R/s⁸R) ⊗[R] B → Λ/s⁸Λ` through a smooth
   `C`. The desingularization statement gives `A → B → B₂ → Λ` with `B₂_s`
   smooth over `R`, and `Λ/s⁸Λ = H_{C}·(Λ/s⁸Λ) ⊆ h_{B₂} mod s⁸Λ`. Hence
   `h_{B₂} + s⁸Λ = Λ`.
5. Since `B₂_s` is smooth, `s ∈ H_{B₂/R}`. Hence `s⁸Λ ⊆ h_{B₂}`, so `h_{B₂} = Λ`
   and `H_{B₂/R} Λ = Λ` (`Ideal.radical_eq_top`).

## Main theorem

`reductionToField_of` states that Lemma 2.8, nilpotent lifting, the
desingularization statement and Lemma 8.3 together imply
`PopescuReductionToFieldStatement`.

Proof (Stacks 07F5). Let `R → Λ` be a regular map of Noetherian rings and assume
the field case.

1. First show that PT holds for `R/I → Λ/IΛ` for every ideal `I`. If not, the
   set of ideals where it fails has a maximal element `I`
   (`set_has_maximal_iff_noetherian`).
2. `R/I` is Noetherian and `R/I → Λ/IΛ` is regular. A nonzero ideal of `R/I` is
   `J/I` with `I < J`, so PT holds for `R/J → Λ/JΛ`.
3. The double quotient isomorphisms `(R/I)/(J/I) ≅ R/J` and
   `(Λ/IΛ)/(J/I)(Λ/IΛ) ≅ Λ/JΛ` (`DoubleQuot.quotQuotEquivQuotOfLE`) transfer PT.
   The key lemma then gives PT for `R/I → Λ/IΛ`, a contradiction.
4. Take `I = 0` and transfer along `R/0 ≅ R`, `Λ/0 ≅ Λ`.
