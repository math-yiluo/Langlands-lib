# Proof of Murre's Lemma 2, first half of case (b)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericNoLargerLiftProof`
proves

```
theorem EtaleLocus.genericNoLargerLift : GenericNoLargerLiftStatement.{u, v}
```

(namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor`). The statement is explained in
`MurreGenericNoLargerLift.md`. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. It imports the statement module and the supporting
modules `MurreGenericLiftDescent` (which imports `MurreGenericLiftMaps`) and
`MurreGenericLiftAlgebra`, whose results (namespace `GenericLift`) are cited by name below.

## Proof

Let `R`, `F`, `R'`, `𝔍`, `ξ` and `y` be as in the statement. Write `f'` for
`Spec R' ⟶ Spec R`. From `MurreConditions F` only (F1a) `ZariskiSheaf`, (F2)
`FilteredColimits` and (F8) `GenericNonLifting` are used. `R'` is noetherian, being of finite
type over `R`.

1. **The prime `P`.** Let `P := y.asIdeal.comap (Ideal.Quotient.mk 𝔍)`, a prime of `R'`
   containing `𝔍`. The hypothesis on `y` says `P ∩ R ≤ nilradical R`. Since `R'` is étale,
   hence formally unramified and essentially of finite type over `R`,
   `mem_minimalPrimes_of_under_le_nilradical` makes `P` a minimal prime of `R'`.
2. **The element `h`.** By `exists_mem_other_minimalPrimes` there is `h ∉ P` lying in every
   other minimal prime. Then every prime not containing `h` contains `P`
   (`le_of_notMem_of_mem_other`). Let `R'_h := Localization.Away h`. Then
   `nilradical R'_h = P R'_h` (`nilradical_away_eq`); it is prime and contains `𝔍R'_h`.
3. **The ring `A`.** Let `K' := 𝔍R'_h · nilradical R'_h ≤ nilradical R'_h`, `A := R'_h/K'`,
   and `I := 𝔍A`. Then:
   - `A` is noetherian;
   - `nilradical A` is prime and is the image of `nilradical R'_h`
     (`isPrime_nilradical_quotient`, `nilradical_quotient_eq_map`);
   - its preimage in `R'` is `P` (`comap_nilradical_quotient`);
   - `I` is the image of `𝔍R'_h`, so it lies in the nilradical and is nilpotent;
   - `I · nilradical A` is the image of `K'`, which is `0`.

   So the point `t := nilradical A` of `Spec A` is a generic point of `Spec A`: every prime
   contains the nilradical. This is the setting of (F8) for `A`, `t`, `I`, the morphism
   `baseOver f' A : Spec A ⟶ Spec R` and `ξ_A := restrictBase f' A 𝔍 ξ`, the restriction of
   `ξ` to `Spec (A/I)`.
4. **No larger lift at `t`** (Murre's step 1). In `A_t` the maximal ideal is the image of
   `t = nilradical A`, so it is the nilradical. Hence `A_t` has dimension zero
   (`Ring.KrullDimLE.of_isMaximal_nilradical`) and is artinian, being noetherian
   (`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`). Its maximal ideal lies over
   `t`, hence over `P` in `R'`. So `noLargerLift_of_isArtinianRing` gives
   `NoLargerLift (f := f') A_t ξ`. By `noLargerLift_restrictBase_iff` this is
   `NoLargerLift (f := baseOver f' A) A_t ξ_A`, the hypothesis of (F8).
5. **(F8)** (Murre's step 2) gives `g₀ ∈ A` with `D(g₀)` nonempty and
   `NoLargerLift (Localization.Away g) ξ_A` whenever `D(g) ⊆ D(g₀)`. Since `D(g₀)` is
   nonempty and `t` is the nilradical, `g₀ ∉ t`. Write `g₀ = x mod K'` with
   `x · (s/1) = r₀/1` in `R'_h`, for some `r₀ ∈ R'` and some power `s` of `h`. Then
   `g₀ ∣ r₀ mod K'` (the image of `r₀` in `A`). That image is `g₀` times a unit, so it is
   not in `t`, and therefore `r₀ ∉ P`. For every multiple `g` of the image of `r₀`,
   `D(g) ⊆ D(g₀)`, so `NoLargerLift (Localization.Away g) ξ_A`.
6. **The neighbourhood.** Take `V := D(h r₀ mod 𝔍)`, open in `Spec (R'/𝔍)`. It contains `y`
   because `h ∉ P` and `r₀ ∉ P`.
7. **At a point `w ∈ V`** (Murre's step 3). Let `Q := w.asIdeal.comap (Ideal.Quotient.mk 𝔍)`,
   so `h ∉ Q`, `r₀ ∉ Q`, and `P ≤ Q`. Make `R'_Q` an `R'_h`-algebra
   (`IsLocalization.localizationAlgebraOfSubmonoidLe`). Then `R'_Q` is the localization of
   `R'_h` at the image of `R' ∖ Q` (`IsLocalization.isLocalization_of_submonoid_le`).
   - *Nilpotency.* `𝔍R'_Q` is the image of `𝔍R'_h ⊆ nilradical R'_h`, so it lies in the
     nilradical of the noetherian ring `R'_Q` and is nilpotent.
   - *(F2).* `B := R'_Q/K'R'_Q` is the localization of `A = R'_h/K'` at the image of
     `R' ∖ Q` (a Mathlib instance for quotients of localizations). That submonoid contains
     the image of `r₀`. By step 5 and `noLargerLift_of_isLocalization`,
     `NoLargerLift (f := baseOver f' A) B ξ_A`. By `noLargerLift_restrictBase_iff` this is
     `NoLargerLift (f := f') B ξ`.
   - *Nakayama.* The quotient map `R'_Q → B` is a surjection of `R'`-algebras with kernel
     `K'R'_Q = 𝔍R'_Q · (nilradical R'_h)R'_Q ≤ 𝔪 · 𝔍R'_Q`, since nilpotents lie in the
     maximal ideal `𝔪` of `R'_Q`. `noLargerLift_of_surjective` gives
     `NoLargerLift (Localization.AtPrime Q) ξ`.

## Relation to Murre's text

Murre, printed p.251 (PDF p.10) of `murre-1965-bourbaki-294-unramified-functors` (SHA-256
`e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`), case (b). Murre assumes
the base is the irreducible component itself and applies (F8) to the base. Here the base
`Spec R'` is replaced by the irreducible open `Spec R'_h`. To satisfy the hypothesis
`I · N = 0` of (F8), it is then replaced by the closed subscheme `Spec A` with the same
underlying space. Murre's passage "using (F2)" to the local rings `𝒪_{S,z}` becomes two
steps: the descent of `MurreGenericLiftDescent`, from basic opens of `Spec A` to the
localization `B` of `A`, and the Nakayama transfer from `B = R'_Q/K'R'_Q` to `R'_Q`. The
transfer is needed because the local ring of `Spec A` at `w` is `B`, not `R'_Q`.
