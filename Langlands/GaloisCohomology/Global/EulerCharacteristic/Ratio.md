# The Euler characteristic ratio of `G_S`

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Ratio.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `G_S` the
Galois group of the maximal extension of `K` in `Ω` unramified outside `S`, and
`ι : PlaceEmbeddings K Ω`. For a finite smooth `G_S`-module `M`, Tate's global Euler characteristic
formula says

`#H⁰(G_S, M) · #H²(G_S, M) / #H¹(G_S, M) = ∏_{w real} #H⁰(K_w, M) / (#M)^{[K:ℚ]_∞}`

where `[K:ℚ]_∞` is the number of infinite places of `K`. This file defines the ratio of the two sides,

`globalEulerRatio ι M = χ(G_S, M) · (#M)^{#∞} / ∏_{w real} #H⁰(K_w, M)`,

so that the formula for `M` is `globalEulerRatio ι M = 1` (`globalEulerRatio_eq_one_iff`), and proves
its elementary properties: invariance under isomorphisms, value `1` on the zero module, positivity
when the places above `#M` lie in `S`.

It also computes the Euler characteristic of a group of order two (the Galois group of a real place):
for a finite module, `#H¹ = #H²` (`OrderTwo.card_cohomology_one_eq_card_cohomology_two`), so that
`χ = #H⁰` (`OrderTwo.eulerCharacteristic_eq_card_cohomology_zero`); at a real place `w` of `K` this is
`eulerCharacteristic_realLocalModule`.

```lean
theorem card_tateQuot_mul_card (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot σ) * Nat.card M = Nat.card (fixedSub σ) * Nat.card (fixedSub (-σ))
theorem card_tateQuot_neg [Finite M] (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot (-σ)) = Nat.card (tateQuot σ)
theorem card_cohomology_one_eq_card_cohomology_two :
    Nat.card (cohomology A 1) = Nat.card (cohomology A 2)
theorem eulerCharacteristic_eq_card_cohomology_zero :
    eulerCharacteristic A = Nat.card (cohomology A 0)
theorem card_cohomology_one_eq_card_cohomology_two_of_isReal :
    Nat.card (cohomology A 1) = Nat.card (cohomology A 2)
theorem eulerCharacteristic_eq_card_cohomology_zero_of_isReal :
    eulerCharacteristic A = Nat.card (cohomology A 0)
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.card_cohomology_one_eq_card_cohomology_two_of_isReal : ∀ {K : Type u} [inst : Field K]
  [NumberField K] (w : NumberField.InfinitePlace K),
  w.IsReal →
    ∀ (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion))
      [inst_2 : Langlands.IsSmoothRep A] [Finite ↑A],
      Nat.card ↑(Langlands.ProfiniteCohomology.cohomology A 1) =
        Nat.card ↑(Langlands.ProfiniteCohomology.cohomology A 2)
@Langlands.GaloisCohomology.eulerCharacteristic_eq_card_cohomology_zero_of_isReal : ∀ {K : Type u} [inst : Field K]
  [NumberField K] (w : NumberField.InfinitePlace K),
  w.IsReal →
    ∀ (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion))
      [inst_2 : Langlands.IsSmoothRep A] [Finite ↑A],
      Langlands.ProfiniteCohomology.eulerCharacteristic A = ↑(Nat.card ↑(Langlands.ProfiniteCohomology.cohomology A 0))
```

## Outline of the proofs

The ratio is a quotient of positive rationals; its properties are direct from the definitions. For the group `{1, c}` of order two, the Tate cohomology is 2-periodic and `#Ĥ⁰ = #Ĥ⁻¹` for a finite module (the Herbrand quotient of a finite module is `1`, through `M^c/(1+c)M` and `ker(1+c)/(1-c)M`, `card_tateQuot_mul_card`), which gives `#H¹ = #H²` and hence `χ = #H⁰`.

- `card_tateQuot_mul_card`: For an involution `σ` of a finite group `M`: `#(M^σ / (1 + σ)M) · #M = #M^σ · #M^{-σ}`.
- `card_tateQuot_neg`: For an involution `σ` of a finite group, `M^σ/(1 + σ)M` and `M^{-σ}/(1 - σ)M` have the same order (the Herbrand quotient of a finite module is `1`).
- `card_cohomology_one_eq_card_cohomology_two`: For a group of order two and a finite module, `#H¹ = #H²`.
- `eulerCharacteristic_eq_card_cohomology_zero`: For a group of order two and a finite module, the Euler characteristic is `#H⁰`.
- `card_cohomology_one_eq_card_cohomology_two_of_isReal`: At a real place `w`, `#H¹(K_w, A) = #H²(K_w, A)` for a finite module `A`.
- `eulerCharacteristic_eq_card_cohomology_zero_of_isReal`: At a real place `w`, the Euler characteristic of a finite module `A` is `#H⁰(K_w, A)`.

## Declarations

`Involution.ker_id_add_eq_fixedSub_neg`, `Involution.card_tateQuot_mul_card`, `Involution.card_tateQuot_neg`, `OrderTwo.act_act`, `OrderTwo.finite_cohomology_one`, `OrderTwo.finite_cohomology_two`, `OrderTwo.card_cohomology_one_eq_card_cohomology_two`, `OrderTwo.eulerCharacteristic_eq_card_cohomology_zero`, `card_cohomology_one_eq_card_cohomology_two_of_isReal`, `eulerCharacteristic_eq_card_cohomology_zero_of_isReal`, `finite_cohomology_of_isReal`, `card_cohomology_eq_of_iso`, `card_eq_of_iso`, `card_cohomology_zero_of_subsingleton`, `card_cohomology_zero_of_forall_eq_one`, `globalEulerRatio`, `finite_realLocalModule'`, `card_cohomology_zero_realLocalModule_pos`, `eulerCharacteristic_realLocalModule`, `prod_card_cohomology_zero_realLocalModule_ne_zero`, `globalEulerRatio_eq_of_iso`, `globalEulerRatio_eq_one_of_subsingleton`, `globalEulerRatio_eq_one_iff`, `eulerCharacteristic_pos_of_mem`, `globalEulerRatio_pos`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), §VIII.7, the second partial Euler–Poincaré characteristic χ₂ and (8.7.4), p. 505; (7.3.5) (archimedean local fields), p. 396.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §5, Theorem 5.1, p. 67 (the formula and its normalization at the archimedean places).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/DefsForms.lean` lines 1–176, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/RealHerbrand.lean` lines 1–154. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `gsRealH0Card_pos` → `card_cohomology_zero_realLocalModule_pos`, `gsEulerRatio_eq_of_iso` → `globalEulerRatio_eq_of_iso`, `gsEulerRatio_eq_one_of_subsingleton` → `globalEulerRatio_eq_one_of_subsingleton`, `eulerChar_gs_pos` → `eulerCharacteristic_pos_of_mem`, `gsEulerRatio_eq_one_iff` → `globalEulerRatio_eq_one_iff`, `globalEulerFormula_iff` → `globalEulerRatio_eq_one_iff`, `eulerChar_eq_gsEulerInfFactor_iff` → `globalEulerRatio_eq_one_iff`, `globalEulerFormulaInf_iff` → `globalEulerRatio_eq_one_iff`, `card_cohomology_one_eq_two` → `card_cohomology_one_eq_card_cohomology_two`, `eulerChar_eq_card_cohomology_zero` → `eulerCharacteristic_eq_card_cohomology_zero`, `eulerChar_eq_card_cohomology_zero_of_isReal` → `eulerCharacteristic_eq_card_cohomology_zero_of_isReal`, `finite_res_gsRealFamily` → `finite_realLocalModule'`, `gsReal_card_cohomology_one_eq_two` → `card_cohomology_one_eq_card_cohomology_two_of_isReal`, `gsReal_finite_cohomology` → `finite_cohomology_of_isReal`, `gsEulerRatio` → `globalEulerRatio`.
