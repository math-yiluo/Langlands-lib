# Discrete valuation ring criterion for universal closedness over a noetherian affine base

Authors: Worker 1042.

Module `Langlands.AlgebraicGeometry.NoetherianValuativeCriterion`. Written for task
`6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism
functor of a projective abelian scheme). The main theorem is
`Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift`; the
auxiliary lemmas are in namespace
`Langlands.AlgebraicGeometry.NoetherianValuativeCriterion`. The module adds no axioms. It sets
`autoImplicit false` and `backward.isDefEq.respectTransparency.types false`; the second option
is one of the FLT lakefile options under which the adapted FLT proofs were written.

## Main theorem

`universallyClosed_of_forall_isDiscreteValuationRing_hasLift f H`: let `R : Type u` be a
commutative noetherian ring, `X : Scheme.{u}`, and `f : X ⟶ Spec R` quasi-compact and locally of
finite type. Suppose that every Mathlib `ValuativeCommSq f` whose valuation ring `S.R` is a
discrete valuation ring has a lift (`H`). A `ValuativeCommSq f` is a commutative square from
`Spec K ⟶ Spec V` to `f`, where `V` is a valuation ring with fraction field `K`; a lift is a
morphism `Spec V ⟶ X` making both triangles commute. Then `f` is universally closed.

This is the existence part of the valuative criterion of universal closedness tested only on
discrete valuation rings, over a noetherian affine base (compare Grothendieck, EGA II, 7.3.8).

## Provenance

The proof adapts three proofs from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic -
Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2",
literature id `anthropic-flt-complete-lean-source-6e837e75`):

- `P2M/Sol/S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift.lean`
  (the same criterion over a ring `B` of finite type over `ℤ`, tested on discrete valuation rings
  with finite residue field);
- `P2M/Sol/S_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes.lean`;
- `P2M/Sol/S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField.lean`.

Licence of the adapted text: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of
the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. FLT
`ATTRIBUTION.md` does not list these files as containing third-party material.

Changes against the FLT proofs:

- Over a ring of finite type over `ℤ`, FLT proves the image of a closed set closed by the Jacobson
  property: a constructible set containing every closed point that is a specialization of one of
  its points is closed. Here the base ring is only noetherian. The image is closed instead by
  Mathlib's `PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`: a
  constructible subset of a prime spectrum that is stable under specialization is closed. So
  `mem_image_of_specializes` handles every specialization `t' ⤳ t`, not only closed points `t`.
- Accordingly the target point `t` of the valuative square is any prime, not a maximal ideal. In
  `exists_coheightOne` the ideal `𝔪` is prime instead of maximal, and the image `mbar` of `𝔪` in
  `C ⧸ 𝔮` is prime (`mbar_isPrime`, from Mathlib's `Ideal.isPrime_map_quotientMk_of_isPrime`)
  instead of maximal; only the localization at `mbar` is used.
- The finiteness of residue fields is dropped everywhere: the FLT hypotheses
  `∀ m maximal, Finite (C ⧸ m)` and the closedness of `t`, and the conclusion
  `Finite (ResidueField S.R)`. The FLT lemmas `isJacobsonRing_int`,
  `finite_of_field_of_moduleFinite_int`, `finite_quotient_mvPolynomial_of_isMaximal`,
  `finite_of_isFiniteLength` and the residue-field paragraph of the FLT domination proof are not
  used.
- The lift hypothesis is an explicit implication
  `∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R → S.commSq.HasLift` instead of FLT's
  instance arguments.
- Style: `haveI`/`letI` are replaced by `have`/`let` (as suggested by the Mathlib linter), the
  deprecated `ENat.lt_one_iff_eq_zero` and `ENat.one_le_iff_ne_zero` by `Order.lt_one_iff` and
  `Order.one_le_iff_ne_zero`, and unused section instances are omitted.

## Auxiliary lemmas

All in namespace `Langlands.AlgebraicGeometry.NoetherianValuativeCriterion`.

- `locallyOfFinitePresentation_of_isNoetherianRing g`: a morphism `g : X ⟶ Spec C` locally of
  finite type over a noetherian ring is locally of finite presentation (on affine opens,
  `RingHom.FinitePresentation.of_finiteType`). FLT text.
- `hasLift_baseChange hP H S hS`: if `iX, f', f, iY` form a pullback square and every valuative
  square of `f` with a discrete valuation ring has a lift, then so does every such square `S` of
  `f'`: compose `S` with the square, lift, and use the pullback property. FLT text with the
  explicit hypothesis.
- `exists_isOpen_inter_closure_subset hs`: every point `x` of a constructible set `s` has an open
  neighbourhood `U` with `U ∩ closure {x} ⊆ s` (induction on constructible sets). FLT text.
- `eq_or_eq_maximalIdeal_of_ringKrullDim_quotient_eq_one q hq p hqp`: in a local ring, if
  `R ⧸ q` has Krull dimension `1`, every prime `p ⊇ q` equals `q` or the maximal ideal. FLT text.
- `exists_coheightOne 𝔭 𝔪 hpm hne s hs`: for primes `𝔭 ≤ 𝔪`, `𝔭 ≠ 𝔪`, of a noetherian ring and
  `s ∉ 𝔭`, there is a prime `𝔮` with `𝔭 ≤ 𝔮 ≤ 𝔪`, `𝔮 ≠ 𝔪`, `s ∉ 𝔮`, and no prime strictly
  between `𝔮` and `𝔪`. Proof: in the local domain `C_𝔪 ⧸ 𝔭 C_𝔪`, which is not a field, apply the
  ported FLT theorem `IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one` to the
  image of `s`, and pull the resulting prime back to `C`.
- `mbar 𝔮 𝔪`: the image `𝔪 (C ⧸ 𝔮)` of `𝔪` in `C ⧸ 𝔮` (an abbreviation). `comap_mbar`: its
  preimage in `C` is `𝔪` when `𝔮 ≤ 𝔪`. `mbar_isPrime`: it is prime when `𝔪` is prime and
  `𝔮 ≤ 𝔪`. `eq_bot_of_lt_mbar`: if no prime lies strictly between `𝔮` and `𝔪`, every prime
  strictly below `mbar` is `⊥`. `height_mbar`: under this hypothesis and `𝔮 ≠ 𝔪`, `mbar` has
  height `1`.
- `exists_valuationSubring_dominates hA`: let `A` be a noetherian local domain of Krull dimension
  `1` with fraction field `K`, and `L` a finite extension of `K` (with compatible `A`-algebra
  structure). Then there is a valuation subring `V` of `L` that is a discrete valuation ring,
  contains the image of `A`, and dominates `A`: `a` lies in the maximal ideal of `A` iff its image
  is a non-unit of `V`. Proof: the Library theorem
  `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates` gives such a `V₀` in `K`;
  the ported FLT theorem
  `ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional` extends it to
  `V` in `L`; domination passes along. FLT text without the residue-field paragraph.
- `exists_valuativeCommSq_of_specializes g x t hxt hne hcov`: let `g : X ⟶ Spec C` be locally of
  finite type over a noetherian ring, `x : X`, and `t` a specialization of `g x`, different from
  it, with no prime strictly between them (`hcov`). Then there is a valuative square `S` of `g`
  whose ring `S.R` is a discrete valuation ring, whose bottom map sends the closed point to `t`,
  and whose top map has range in `closure {x}`. Proof: let `𝔮` be the prime of `g x`,
  `K₀ = Frac (C ⧸ 𝔮)` and `A` the localization of `C ⧸ 𝔮` at `mbar 𝔮 t`, a noetherian local domain
  of dimension `1` (`height_mbar`, `IsLocalization.AtPrime.ringKrullDim_eq_height`). The fibre
  `X_K₀` of `g` over `Spec K₀` is a Jacobson space (`LocallyOfFiniteType.jacobsonSpace`); choose a
  closed point `z'` of the closure of a point `x'` over `x`. Its residue field `L` is finite over
  `K₀` (`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`). `exists_valuationSubring_dominates`
  gives a discrete valuation ring `V ⊆ L` dominating `A`. The square has top map
  `Spec L ⟶ X_K₀ ⟶ X` and bottom map `Spec V ⟶ Spec C`; domination gives that the closed point of
  `Spec V` maps to `t`, and `x ⤳ z'` gives the range condition.
- `mem_image_of_specializes g H Z hZ hZc ht' h`: for `g` locally of finite type over a noetherian
  ring with lifts for all valuative squares with a discrete valuation ring, a closed set `Z ⊆ X`
  with constructible image, a point `t'` of the image and a specialization `t' ⤳ t`, the point `t`
  is in the image. Proof: if `t' ≠ t`, take an open `U ∋ t'` with `U ∩ closure {t'} ⊆ g(Z)`
  (`exists_isOpen_inter_closure_subset`) and a basic open `D(s) ⊆ U` containing `t'`;
  `exists_coheightOne` gives `𝔮` between `t'` and `t` with `s ∉ 𝔮`, so `𝔮 = g z` for some `z ∈ Z`.
  `exists_valuativeCommSq_of_specializes` for `z` and `t` gives a square; the lift sends the
  closed point of `Spec V` to a point of `closure {z} ⊆ Z` over `t`.

## Proof of the main theorem

By the ported FLT theorem
`AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial` it
suffices that, for every finite type `ι`, the second projection `g` of the pullback of `f` along
`Spec (MvPolynomial ι R) ⟶ Spec R` is a closed map. The ring `MvPolynomial ι R` is noetherian;
`g` is quasi-compact and locally of finite type, so the pullback is a noetherian scheme and every
closed set `Z` of it is constructible. `g` is locally of finite presentation
(`locallyOfFinitePresentation_of_isNoetherianRing`), so `g(Z)` is constructible
(Chevalley, `Scheme.Hom.isConstructible_image`). Lifts for valuative squares of `g` with a
discrete valuation ring come from those of `f` (`hasLift_baseChange`). By
`mem_image_of_specializes`, `g(Z)` is stable under specialization, hence closed
(`PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`).

## Dependencies

- Library: `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates`.
- Ported in the same contribution:
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial`,
  `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one`,
  `Langlands.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional`.
- `Mathlib`.
