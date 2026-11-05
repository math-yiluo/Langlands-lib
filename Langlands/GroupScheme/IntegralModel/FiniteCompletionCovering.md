# Parabolic-left integral coverings at finite completions

This module specializes the local covering of
`Langlands.GroupScheme.IntegralParabolicCovering` to an actual finite place
`v : FinitePlace F` of a number field `F : Type u`. The ring is the completed
integers `v.adicCompletionIntegers F`, and its fraction field is
`FiniteCompletion F v`, which is by definition `v.adicCompletion F`. The
quotient is still not constructed. As in the parent module, these are
explicit hypotheses on a morphism `q : M.group.X ⟶ Q` over
`Spec (v.adicCompletionIntegers F)`:

* `q.left` is flat, surjective and quasi-compact, and `Q` is proper;
* the model morphism `φ.hom.hom.hom` is a monomorphism, `N.IsSmooth` holds,
  and `N.HasConnectedSpecialFibre` holds;
* the exact coset criterion `hfib`: for every test object `T` and points
  `g h : T ⟶ M.group.X`, `g ≫ q = h ≫ q` holds exactly when `g⁻¹ * h` lies in
  the image of `φ.hom` on `T`-points.

The parent module needs three properties of the completed integers, and they
are not hypotheses here. `ValuationRing` comes from Mathlib, since the
completed integers form a valuation subring of `v.adicCompletion F`. Finiteness
of the residue field is the published instance
`Langlands.Global.CompletionResidue.finite_adicResidueField`. Completeness for
the maximal ideal is the published theorem
`Langlands.ClassField.Global.isAdicComplete_adicCompletionIntegers`.

## Declarations

* `finiteCompletion_range_mul_integralPoints_eq_univ`: for integral models
  `M` of `G` and `N` of `P` over the completed integers, and `φ : N.Hom M f`
  over `f : P ⟶ G` of `FiniteCompletion F v`-groups,
  `Set.range (rationalPoints.map f) * M.integralPoints = Set.univ`.
* `finiteCompletion_coefficientIntegralPoints_covering`: let `p : P ⟶ G` be
  a morphism of group schemes over `F` itself. Let `M` and `N` be integral
  models of `baseChanged F (FiniteCompletion F v) G` and of the corresponding
  base change of `P`. Let `φ` lie over the base change of `p`. Then
  `Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
  M.coefficientIntegralPoints F (FiniteCompletion F v) = Set.univ`. This is
  the literal parabolic-left product of the target `IsIntegralIwasawaFamily`
  at the place `v`, with `M.coefficientIntegralPoints F (FiniteCompletion F v)`
  in place of `K v`.
* `finiteCompletion_exists_factor`: under the same hypotheses, every
  `g : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))` equals
  `P.affinePointsTarget p _ h * k` for a pair `(h, k)`. Here
  `h : P.affinePoints (CommAlgCat.of F (FiniteCompletion F v))` and `k` is an
  element of the subgroup `M.coefficientIntegralPoints F (FiniteCompletion F v)`.
* `finiteCompletionParabolicIntegralFactor` is a chosen such pair, obtained by
  `Classical.choose`. `finiteCompletionParabolicIntegralFactor_spec` states
  that its components multiply to `g`. The pair is not claimed to be unique
  or canonical.

## Implemented proof

The first theorem installs completeness as a local instance from
`isAdicComplete_adicCompletionIntegers`. It then applies
`range_mul_integralPoints_eq_univ` of the parent module, and instance search
finds the valuation-ring and finite-residue instances. The second theorem
feeds this equality to the published `IntegralModel.coefficientIntegralPoints_covering`
as its covering hypothesis `hcover`, applied to the base-changed map
`(GroupScheme.baseChange (baseMap F (FiniteCompletion F v))).map p`. That
theorem moves the product to the original group's points over
`CommAlgCat.of F (FiniteCompletion F v)`. The factorization theorem unpacks
membership of `g` in the pointwise product, which is `Set.univ`. The chosen
pair is that existential's witness.

## Provenance and scope

This is a derived step in the proof of Getz-Hahn Theorem B.2.5 (printed
pp.543-544, PDF pp.548-549). The local equality there is
`G(F_v) = P(F_v) G(O_v)` for almost all `v`, and this module states it at one
place where the hypotheses hold. The October 2026 errata (all five pages) make
no correction to that passage. In the source, `O_v` is Henselian. Here the
parent module uses completeness of the actual completed integers, which the
published theorem supplies.

The module does not construct reductive or parabolic integral models, the
quotient `Q`, or its coset criterion. It does not show that any of these exist
at almost all places. It does not prove that
`M.coefficientIntegralPoints F (FiniteCompletion F v)` is compact or maximal,
and it says nothing about adelic points or regular-function integrality. It
does not prove `Langlands.Global.IntegralIwasawaFamily.ExistenceStatement`.
