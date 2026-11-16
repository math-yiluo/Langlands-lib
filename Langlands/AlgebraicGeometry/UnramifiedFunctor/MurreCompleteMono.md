# The closed-fibre charts are monomorphisms

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteMono`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. This module supports the proof
of Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`; Bourbaki exp. 294, Case I,
Step 2a). Murre's Lemma 3 needs each chart element to be a monomorphism. This module proves that
`ξ_y = chartElem e hF3 y`, viewed as a morphism `Spec B_y → F`, is one
(`chartElem_isMonoElement`).

## Agreement on `U ×_S U` (generic part)

Throughout, `U` is an object over `S = Spec R` and `ξ ∈ F(U)`.

* `map_injective_of_flat` is condition (F1b) in the form used here: restriction along a flat,
  surjective, quasi-compact morphism is injective (`FaithfullyFlatSheaf`).
* `AgreeAlong U ξ β`: for `β : T ⟶ U ×_S U`, the two pullbacks of `ξ` to `T` along the
  projections are equal.
  * It is invariant under equality of `β` (`agreeAlong_congr`).
  * It is stable under precomposition (`agreeAlong_comp`).
  * It descends along flat surjective quasi-compact morphisms by (F1b) (`agreeAlong_of_comp`).
* `AgreeAtPt U ξ a`: agreement along `Spec κ(a) ⟶ U ×_S U` at a point `a`. Agreement at `a`
  implies agreement along any morphism `Spec L → U ×_S U` from a field through `a`
  (`agreeAlong_of_agreeAt`). By (F1b) the converse holds too (`agreeAt_of_agreeAlong`), since
  `Spec L ⟶ Spec κ(a)` is faithfully flat (`MurreCompleteSeparated`).

## The chart

`chartU e y = ovR R B_y` is `Spec B_y` over `Spec R`. `chartP e y` is `Spec B_y ×_S Spec B_y`,
with projections `chartFst` and `chartSnd`. The instances say that `chartU` is affine, formally
unramified and locally of finite type. `chartU_isFinite` says that `Spec B_y → Spec R` is finite,
because `B_y` is a finite `R`-module.

* `chart_eq_of_closed`: let `L` be a field lying over the closed point of `Spec R`. Two
  `S`-morphisms `Spec L → Spec B_y` that restrict `ξ_y` to the same element are equal. Here `L`
  kills `m`, so `chart_inj_level` at level `0` applies.
* `chart_mem_range_of_closed`: a point of `chartP` over the closed point of `Spec R` at which the
  two pullbacks of `ξ_y` agree lies on the diagonal. Apply `chart_eq_of_closed` to the residue
  field of the point, then the Library's `lift_mem_range_diagonal`.
* `chart_mem_range`: every point `a` of `chartP` at which the two pullbacks agree lies on the
  diagonal. If `a` lies over the closed point, use the previous item. Otherwise `chartP` is
  affine and noetherian, and `a` specializes to a closed point `b`. Since `chartP` is finite over
  `Spec R`, `b` lies over the closed point. `exists_dvr_spec` (`MurreCompleteSeparated`) gives a
  discrete valuation ring `V` and `n : Spec V ⟶ chartP`, with the closed point mapping to `b`
  and the generic point mapping to `a`. Agreement at `a` gives agreement over `Spec Frac(V)`, and
  hence over `Spec V` by (F6) (`ValuativeSeparation`). After restriction to the spectrum of the
  residue field of `V`, `chart_eq_of_closed` makes `n ≫ chartFst` and `n ≫ chartSnd` equal.
  Since `Spec B_y` is formally unramified over `S`, the Library's `eq_of_isLocalRing` then gives
  `n ≫ chartFst = n ≫ chartSnd` on all of `Spec V`. So the image `a` of the generic point lies on
  the diagonal.
* `chartElem_isMonoElement`: assume (F1b) and (F6), and let `h₁, h₂ : T ⟶ Spec B_y` restrict
  `ξ_y` to the same element. By the Library's `eq_of_forall_mem_range_diagonal`, it suffices
  that for every point `z` of `T`, the image of `z` under `(h₁, h₂) : T ⟶ chartP` lies on the
  diagonal. Agreement along `(h₁, h₂)` restricts to `Spec κ(z)`, giving agreement at that image
  point (`agreeAt_of_agreeAlong`), and `chart_mem_range` concludes.
