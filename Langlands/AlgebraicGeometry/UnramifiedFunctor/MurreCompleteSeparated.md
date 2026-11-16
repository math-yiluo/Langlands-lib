# Separatedness from discrete valuation rings

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteSeparated`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. A supporting module of the proof
of Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I,
Step 2a). Murre states that the representing scheme is separated without an argument; this
module supplies the argument used here: the valuative criterion of separatedness, reduced to
discrete valuation rings for schemes locally of finite type over a noetherian affine base, so
that condition (F6) (`ValuativeSeparation`) applies. The reduction to discrete valuation rings is
the standard one (EGA II 7.2.3 for the noetherian case); the proof below is written directly.

## Discrete valuation rings realizing specializations

* `exists_dvr_dominates`: a noetherian local domain `D` that is not a field has an injective
  ring map `ι : D → V` to a discrete valuation ring `V` with `ι⁻¹(m_V) = m_D`. This is the
  ported Anthropic FLT theorem
  `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates` (a discrete valuation
  subring of `Frac D` dominating `D`), with `ι` the corestriction of `D → Frac D`.
* `exists_dvr_of_lt`: for primes `a < b` of a noetherian ring `C` there is `φ : C → V`,
  `V` a discrete valuation ring, with `ker φ = a` and `φ⁻¹(m_V) = b`. Apply the previous lemma to
  `D = (C/a)_{b/a}`, a noetherian local domain; it is not a field because the image of an
  element of `b ∖ a` is a nonzero element of its maximal ideal. `φ` is
  `C → C/a → D → V`; its kernel is `a` because `C/a → D` and `ι` are injective, and the
  preimage of `m_V` is `b` by `IsLocalization.AtPrime.to_map_mem_maximal_iff`.
* `exists_dvr_spec`: the scheme version. If `P` is affine with noetherian global sections and
  `a ⤳ b`, `a ≠ b`, there is a discrete valuation ring `V` and `n : Spec V ⟶ P` sending the
  closed point to `b` and the point of `Spec (Frac V)` to `a`. Transport `a, b` along
  `P.isoSpec`, where specialization is inclusion of primes (`PrimeSpectrum.le_iff_specializes`),
  and take `n = Spec φ ≫ P.isoSpec.inv`; the point of `Spec (Frac V)` goes to
  `φ⁻¹(0) = ker φ`.

## Morphisms from spectra of fields

* `epi_specMap_of_isField`: for a ring map `d` between fields, `Spec d` is flat and surjective,
  hence an epimorphism of schemes (`Flat.epi_of_flat_of_surjective`).
* `fromSpecResidueField_comp_eq`: if `α : Spec K ⟶ X` (`K` a field) satisfies
  `α ≫ g₁ = α ≫ g₂`, then `X.fromSpecResidueField x ≫ g₁ = X.fromSpecResidueField x ≫ g₂` for
  `x` the image of `α`: `α` factors as `Spec d ≫ X.fromSpecResidueField x`
  (`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`) and `Spec d` is an
  epimorphism.
* `comp_eq_of_fromSpecResidueField`: conversely, agreement on `Spec κ(x)` gives agreement after
  every `β : Spec L ⟶ X` with image `x`, by the same factorization of `β`.

## The separatedness criterion

Let `R` be noetherian and `q : Y ⟶ Spec R` locally of finite type.

* `range_subset_of_closedPoint_mem`: a morphism from the spectrum of a local ring whose closed
  point lands in an open `U` has range in `U` (every point specializes to the closed point).
* `eq_of_dvr`: suppose that two `Spec R`-morphisms from the spectrum of a discrete valuation
  ring `V` to `Y` that agree on `Spec (Frac V)` are equal. Let `W` be a valuation ring with
  fraction field `K` and `l₁, l₂ : Spec W ⟶ Y` two `Spec R`-morphisms agreeing on `Spec K`.
  Then `l₁ = l₂`. Proof: choose affine opens `U₁ ∋ l₁(c)`, `U₂ ∋ l₂(c)` (`c` the closed point);
  `lⱼ` factors through `Uⱼ`. The fibre product `P = U₁ ×_{Spec R} U₂` is affine and locally
  noetherian (locally of finite type over `Spec R`), so its ring of global sections is
  noetherian (`IsLocallyNoetherian.component_noetherian`). Let `m : Spec W ⟶ P` be the pair,
  `a` the image of the generic point and `b = m(c)`, so `a ⤳ b`; let `g₁, g₂ : P ⟶ Y` be the
  two projections followed by the inclusions. Since `l₁, l₂` agree on `Spec K`,
  `fromSpecResidueField_comp_eq` gives `g₁ = g₂` on `Spec κ(a)`. If `a = b`, evaluating at the
  point of `Spec κ(a)` gives `g₁(b) = g₂(b)`. Otherwise `exists_dvr_spec` gives
  `n : Spec V ⟶ P`; the morphisms `n ≫ g₁` and `n ≫ g₂` lie over `Spec R` (pullback square) and
  agree on `Spec (Frac V)` (`comp_eq_of_fromSpecResidueField`), so they are equal by hypothesis,
  and evaluating at the closed point gives `g₁(b) = g₂(b)`. In both cases `l₁(c) = l₂(c)`.
  Hence both `lⱼ` factor through the affine open `U₁`; the morphism `U₁ ⟶ Spec R` is a
  morphism of affine schemes, hence separated (`IsSeparated.of_isAffineHom`), and the two
  factorizations are lifts of one valuative square, so they agree
  (`IsSeparated.valuativeCriterion`).
* `isSeparated_of_dvr`: under the same hypothesis, `q` is separated. `Y` is locally noetherian
  (`LocallyOfFiniteType.isLocallyNoetherian`), so `q` is quasi-separated and Mathlib's
  `IsSeparated.of_valuativeCriterion` reduces separatedness to the uniqueness of lifts, which is
  `eq_of_dvr`.
* `isSeparated_of_representableBy`: if `F : (Over (Spec R))ᵒᵖ ⥤ Type v` satisfies (F6)
  (`ValuativeSeparation`) and is represented by `Over.mk q`, then `q` is separated. Two
  morphisms `l₁, l₂ : Spec V ⟶ Y` over `Spec R` give elements `e.homEquiv lⱼ` of `F(Spec V)`
  whose restrictions to `Spec (Frac V)` are the elements of the restricted morphisms
  (`RepresentableBy.homEquiv_comp`), hence equal; (F6) makes the elements equal, and
  injectivity of `e.homEquiv` gives `l₁ = l₂`.
