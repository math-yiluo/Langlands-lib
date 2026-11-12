# Root fixers of a bounded set are determined by a finite subset

For `P : ParahoricBuildingData G` (any field `F`, group scheme `G` and building
data in universe `u`), a set `Ω : Set P.Apartment` with `P.IsBoundedSubset Ω`
(every affine functional on `A` is bounded above on `Ω`), and a point `x₀ ∈ Ω`,
this module proves that some finite `Ω' ⊆ Ω` with `x₀ ∈ Ω'` satisfies

```text
P.rootFixer a Ω' = P.rootFixer a Ω    for every relative root a,
```

that is `U_{a,Ω',0} = U_{a,Ω,0}`. Hence also `G(F)^♯_{Ω'} = G(F)^♯_Ω` and
`P_{Ω'} = P_Ω`. No apartment axioms are assumed. Only the existence of opposite
factor pairs is used, and that is proved in the Library.

## Declarations

* `ParahoricBuildingData.exists_finite_subset_rootFixer_eq_of_mem`: for one
  relative root `a`, some finite `Ω' ⊆ Ω` with `x₀ ∈ Ω'` has
  `P.rootFixer a Ω' = P.rootFixer a Ω`.
* `ParahoricBuildingData.exists_finite_subset_rootFixer_eq`: one finite
  `Ω' ⊆ Ω` with `x₀ ∈ Ω'` works for all relative roots at once.
* `ParahoricBuildingData.exists_finite_subset_parahoric_eq`: some finite
  `Ω' ⊆ Ω` with `x₀ ∈ Ω'` has `P.sharpFixer Ω' = P.sharpFixer Ω` and
  `P.parahoric Ω' = P.parahoric Ω`.
* `ParahoricFiniteReductionStatement`: the proposition that for every
  nonarchimedean local field `F`, affine group scheme `G` over `F` and
  `P : ParahoricBuildingData G`, every bounded `Ω` and `x₀ ∈ Ω` admit such a
  finite `Ω'` for all relative roots. Its binders are those of the Library target
  `RootGroupActionAxiomStatement`, without the apartment-axiom hypothesis.
* `parahoricFiniteReduction : ParahoricFiniteReductionStatement.{u}`: its proof,
  applying `exists_finite_subset_rootFixer_eq`.

A private helper, `mem_filtration_zero_iff`, records that for
`u ∈ U_a(F) ∖ {1}` and a point `y`, `u ∈ U_{a,y,0}` if and only if
`ψ^u_a(y) ≥ 0`. Here `ψ^u_a = P.reflectionFunctional a u`, and
`coe_reflectionFunctional_apply` identifies its value at `y` with `y_a(u)`.

## Implemented proof

**One root.** Fix `a` and set `φ = P.reflectionFunctional a 1`, an affine
functional with derivative `a`. Boundedness of `Ω` applied to `-φ` gives `M` with
`-φ(x) ≤ M` for `x ∈ Ω`. For each affine functional `ψ`, let `w ψ` be a point of
`Ω` where `ψ` is negative if one exists (chosen with `Exists.choose`), and `x₀`
otherwise. Let `T` be the set of functionals `ψ^g_a`, `g ∈ U_a(F) ∖ {1}`, with
`|ψ^g_a(x₀)| ≤ |φ(x₀)| + |M|`. It is finite by
`ValuationBuildingData.finite_bounded_reflectionFunctionals_of_oppositePairs`
together with `ParahoricBuildingData.hasOppositeFactorPairs`. Take
`Ω' = insert x₀ (w '' T)`. It is finite and contained in `Ω`.

`P.rootFixer a Ω ≤ P.rootFixer a Ω'` is `rootFixer_anti`. Conversely, let
`u ∈ U_{a,Ω',0}` with `u ≠ 1`, write `ψ = ψ^u_a`, and suppose `ψ(x) < 0` for
some `x ∈ Ω`. Since `x₀ ∈ Ω'`, `ψ(x₀) ≥ 0`. Because `ψ` and `φ` have the same
derivative, `ψ(x) - ψ(x₀) = φ(x) - φ(x₀)` (`AffineMap.linearMap_vsub`). So
`0 ≤ ψ(x₀) < φ(x₀) - φ(x) ≤ φ(x₀) + M`, and `ψ ∈ T`. Then `w ψ ∈ Ω'` is a
point where `ψ` is negative, contradicting `u ∈ U_{a,w ψ,0}`. Hence
`ψ ≥ 0` on `Ω`, so `u ∈ U_{a,Ω,0}`.

**All roots.** The relative roots form a finite set (`finite_relativeRoots` for
the split torus, which needs `Smooth G.X.hom` from
`P.isConnectedReductive.smooth`). Choose `Ω'_a` for each root `a` as above and
take `Ω' = insert x₀ (⋃ a, Ω'_a)`. It is finite (`Set.finite_iUnion`) and
contained in `Ω`. For each `a`, `Ω'_a ⊆ Ω' ⊆ Ω` gives
`U_{a,Ω,0} ≤ U_{a,Ω',0} ≤ U_{a,Ω'_a,0} = U_{a,Ω,0}` by `rootFixer_anti`.

**Sharp fixer and parahoric.** `P.sharpFixer Ω = ⨆ a, P.rootFixer a Ω`, so
equality of all root fixers gives `P.sharpFixer Ω' = P.sharpFixer Ω`
(`iSup_congr`). Then `P.parahoric Ω' = P.parahoric Ω` follows by unfolding
`parahoric` as `Z(F)^0 ⊔ G(F)^♯`.

## Provenance and scope

This is an internal lemma for the proof of KP Axiom 4.1.8(2) for supplied data
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Lemma 7.7.4 and
Proposition 7.7.5(1), printed pp. 268–269). KP prove
`G(k)^0_Ω = ⋂_{x ∈ Ω} G(k)^0_x` first for finite `Ω` by induction, then for a
general `Ω` as an increasing union of finite sets, using finiteness of
`N^*_x / Z^*`. For bounded `Ω` the present lemma replaces that limit step: it
reduces `U_{a,Ω,0}`, and hence `P_Ω`, to a finite subset of `Ω`. The argument is
the discreteness of the jumps `ψ^u_a` of the filtration of `U_a(F)` (KP
Remark 4.1.7). The module makes no external assertion beyond those already in
the Library.
