# Step 2a of Murre's induction: the complete local step

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteLocalStepProof`. This module
contains `Langlands.AlgebraicGeometry.UnramifiedFunctor.murreCompleteLocalStep`, a proof of
`MurreCompleteLocalStepStatement.{u, v}`. The statement lives in the Library module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts`.

## Statement

* `R : CommRingCat.{u}` is a local noetherian ring, complete for its maximal ideal `m`.
* `F : (Over (Spec R))ᵒᵖ ⥤ Type v` satisfies `MurreConditions F`.
* `F` is representable by a separated, locally of finite type, formally unramified scheme over
  the punctured spectrum.
* `F` is so representable over each `Spec (R/m^(k+1))`.

Then `F` itself is so representable (`UnramifiedRepresentable F`). This is Step 2a of Case I of
Murre's proof of his criterion (Bourbaki exp. 294, Theorem 1).

## The proof

The theorem unpacks the two representability hypotheses. That gives `X' → U` over the punctured
spectrum `U`, and the schemes `Y k → Spec (R/m^(k+1))` with their representations `e k`. It then
applies `unramifiedRepresentable_of_chartEtale` (`MurreCompleteAssembly`), discharging its
remaining hypothesis with `chartElem_infinitesimallyEtaleAt` (`MurreCompleteEtale`). The
argument, which follows Murre's outline, runs through the supporting modules in this order:

1. `MurreCompleteSeparated`: a scheme locally of finite type over a noetherian base that
   represents a presheaf with (F6) is separated, via dominating discrete valuation rings.
2. `MurreCompleteLimit`: inverse limits of compatible towers of finite algebras over a complete
   local ring.
3. `MurreCompleteFibre`: for a point `y` of `Y 0`, the stalks `B_k = 𝒪_{Y k, y}` form a tower
   with surjective transitions of kernel `m^(k+1) B_(k+1)`. `B_0` is a field, finite over `R/m`.
4. `MurreCompleteChart`: the chart ring `B_y = lim B_k`. It is complete, local, noetherian,
   finite and formally unramified over `R`. The element `ξ_y ∈ F(Spec B_y)` comes from (F3).
   This module also proves pro-representability at the closed point, the covering of the
   closed-fibre field points, and infinitesimal étaleness at the closed point.
5. `MurreCompleteMono`: `ξ_y` is a monomorphism, by (F1b), (F6) and the closed-fibre
   uniqueness.
6. `MurreCompleteAssembly`: Murre's Lemma 3 (`ChartGluing.murreChartGluing`) applied to the
   charts `X'` and `Spec B_y` glues a representing scheme, which is separated and formally
   unramified. This needs infinitesimal étaleness of `ξ_y` away from the closed point.
7. `MurreCompleteEtaleCover`: `B_y` is a quotient of a local ring `L` that is finite étale over
   `R` (primitive element, Hensel, Nakayama).
8. `MurreCompletePunctured`: finite algebras over `R` are complete, and `ξ_y` is
   pro-representable on complete local noetherian `R`-algebras.
9. `MurreCompleteEtaleLevel`: the Library's étale-locus criteria for `Spec (L/I)`, with explicit
   levels.
10. `MurreCompleteStar`: the lifting argument with (F7) at the points `w` with
    `dim L/P_w = 1`.
11. `MurreCompleteHet`: the Library's lifting condition `KillAt` at such points, using (F5).
12. `MurreCompleteEtale`: infinitesimal étaleness at every non-closed point. Prove it at a point
    with `dim L/P_w = 1` above the given one, where the level comes from `X'`, then pass to the
    given point by generization.

The proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. It does not use
`MurreLocalStepStatement`, `MurreLocalStepPartsStatement`, `MurreCriterionStatement`,
`MurreProofStepsStatement` or any statement about abelian schemes or Picard functors.
