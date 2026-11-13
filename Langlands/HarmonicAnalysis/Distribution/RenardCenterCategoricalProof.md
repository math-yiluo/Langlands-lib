# Renard II.3.13 Corollary: the categorical comparison (algebraic part)

Worker 42, Task 5531 (with Worker 108). Source: David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered `renard-2026-representations-groupes-reductifs-padiques`:
I.1.7, Theorem (printed pp.12–13 / PDF pp.18–19), and II.3.13, Corollary and
its proof (printed pp.55–56 / PDF pp.61–62).

This helper module, in namespace
`Langlands.HarmonicAnalysis.Distribution.RenardCenter`, proves the algebraic part
of the second conjunct `CategoricalCenterStatement` of the published
`RenardCenter.Statements`. It does not prove a published statement by
itself. Its final theorem, `categoricalCenterStatement_of`, derives
`CategoricalCenterStatement.{uG, uM}` from three hypotheses: the published
propositions `RenardEssentialProducts.Statements` and
`RenardCompletion.Statements`, and the centrality specification
`CentralitySpecification μ pr` for every right product `pr` satisfying
`RightProductSpecification`. The analytic centrality theorem is proved in a
separate helper module. The module imports only the published statement module
`RenardCenterStatements` and the published proof module
`NondegenerateModuleNaturalEndClassificationProof` (Renard I.1.6).

## I.1.7: the commutant is the categorical center

Let `A` be a ring with idempotents (`hA : IsIdempotented A`). The published
`NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA` sends a
commuting compatible right family `x` (a member of the centralizer of the
canonical image of `A` in the published completion
`IdempotentedRingRightLimit A`) to the natural endomorphism of the identity
functor by which `x` acts on every nondegenerate module. This is the map of
Renard's Lemma in I.1.7. `fromCommutantRingHom_bijective` proves that it is
bijective, which is the first assertion of the Theorem of I.1.7.

* `familyNaturalEnd_injective`: the published action
  `IdempotentedRingRightLimit.familyNaturalEnd` of all compatible families on
  the forgetful functor is injective. The published I.1.6 proof gives
  `familyRecovery`: evaluating the action back to a family recovers `x`. So two
  families with the same action are equal.
* `fromCommutantRingHom_injective`: the underlying natural transformation of
  `fromCommutantRingHom x` is `familyNaturalEnd x`, so injectivity of the
  family action gives injectivity of the map on the commutant.
* `fromCommutantRingHom_surjective`: take a central natural endomorphism `z`,
  its underlying transformation `θ` of the forgetful functor, and the family
  `x := toFamilyRingHom θ` of Renard's construction `θ ↦ θ_A`. The published
  I.1.6 `naturalEndRecovery` gives `familyNaturalEnd x = θ`. `x` commutes with
  every canonical image `a`: both products act through the family action, and
  on each module the action of the canonical image of `a` is the original
  scalar action of `a` (`canonical_act`). The components of `z` are
  `A`-linear, so `θ` commutes with that action. Injectivity of the family
  action then gives `canonical a * x = x * canonical a`. Hence `x` lies in the
  commutant, and `forgetRingHom_injective` identifies
  `fromCommutantRingHom x` with `z`.

## II.3.13: commutant elements and invariant distributions

Fix the right product `pr`, its `RightProductSpecification` `hpr`, and an
additive equivalence `E` of the right essentially compact distributions with
the completion, satisfying `ComparisonSpecification μ hA pr E` (`hE`).

* `comparison_hecke`: if `H` is the right essentially compact lift of a Hecke
  density `h`, then `E H` is the canonical image of `h`. This uses the canonical
  clause of `hE` and equality of lifts in the full dual.
* `comparison_commutes_iff`: for right essentially compact `T`, the coordinate
  `E T` commutes with every canonical image if and only if
  `T * h = h * T` for all Hecke densities `h`, with the two full Hecke
  actions. The fourth clause of `AlgebraLaws` in `hpr` gives a lift `H` of `h`
  with `pr T H = T * h` and `pr H T = h * T`. The product clause of `hE` turns
  `pr T H = pr H T` into equality of the completion products of `E T` and the
  canonical image of `h`, and conversely.
* `symm_commutes_hecke`: for a commutant element `x`, `E⁻¹ x` commutes with
  both Hecke actions. Apply `comparison_commutes_iff` to `E⁻¹ x`, whose image
  under `E` is `x`, and use `NondegenerateModuleCenter.commutes`.
* `exists_commutantInvariant`: under `CentralitySpecification μ pr` (`hC`),
  there is a bijection `Φ` from the commutant to the subtype of
  conjugation-invariant distributions in `essentiallyCompact μ`, whose
  underlying distribution is `E⁻¹ x`. The second clause of `hC` turns Hecke
  commutation into conjugation invariance. Its third clause puts invariant
  distributions in the two-sided module `essentiallyCompact μ`. Injectivity
  comes from injectivity of `E⁻¹`. For surjectivity, a two-sided essentially
  compact invariant `T` is right essentially compact, since
  `essentiallyCompact μ` is the infimum of the right and left submodules. By
  `hC` and `comparison_commutes_iff`, `E T` is in the commutant
  (`mem_commutantSubring_iff`), and `Φ (E T)` has distribution `T`.

## The comparison `C`

`exists_categoricalComparison` takes `hpr`, the two-sided product
specification `TwoSidedProductSpecification μ pr pl p` (`hp`), `hE` and `hC`.
It produces `C` with `CategoricalComparisonSpecification.{uG, uM} μ hA p E C`.
Let `F := fromCommutantRingHom.{uG, max uG uM} hA`, bijective by the I.1.7
part, and `Fe` the equivalence from the commutant to the center that it
defines. Then `C := Φ ∘ Fe⁻¹`, that is, `C z := Φ (Fe⁻¹ z)` for `z` in the
center (in Lean, `Fe.symm.trans (Equiv.ofBijective Φ hΦ)`). The center
carries the published ring `NondegenerateModuleCenter.ring` and the commutant
the published `commutantRing`. Since `F` is a ring homomorphism, `Fe⁻¹`
preserves addition, multiplication and one. The clauses follow.

* Additivity: `Φ (x + y)` has distribution `E⁻¹ (x + y) = E⁻¹ x + E⁻¹ y`. The
  commutant addition is the completion addition, and `E` is additive.
* Products: for `x = Fe⁻¹ z` and `y = Fe⁻¹ w`, the second clause of `hp`
  supplies right lifts `tr` and `ur` of `Φ x` and `Φ y`, with
  `p (Φ x) (Φ y) = pr tr ur` in the full dual. Equality in the full dual
  identifies `tr = E⁻¹ x` and `ur = E⁻¹ y`. By the product clause of `hE`,
  `E (pr tr ur)` is the completion product of `x` and `y`. This is the
  commutant product of `x` and `y`, so `pr tr ur = E⁻¹ (x * y)`, which is the
  distribution of `Φ (x * y)`.
* Unit: `Fe⁻¹ 1 = 1`, whose value is the completion unit. The unit clause of
  `hE` gives `d` with distribution `dirac 1` and `E d = unit`, so `C 1` has
  distribution `dirac 1`.
* The last clause: for `z`, take `x := Fe⁻¹ z` and `T := E⁻¹ x`. Then `T`
  has the distribution of `C z`, `x = E T`, and `F x = z`.

The left product `pl` enters only through `hp`. The first clause of
`CentralitySpecification` (center of the right product algebra equals Hecke
commutation) is not used here.

## The categorical-center statement

`categoricalCenterStatement_of` instantiates the previous theorem. For each
group, `RenardCompletion.Statements` provides `hA`, `pr`, its right
specification, and `E` with its comparison specification.
`RenardEssentialProducts.Statements` provides a left product `pl`, and for
the pair `pr, pl` a two-sided product `p` with its specification. The
centrality hypothesis provides `CentralitySpecification μ pr`.
`exists_categoricalComparison` provides `C`. These data are exactly the
witnesses and conjuncts required by `CategoricalCenterStatement`. The
universes are those of the target, including the module universe
`max uG uM` of the categorical center.
