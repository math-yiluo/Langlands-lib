# Murre's charts over a noetherian affine base, from Lemma 2

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCharts`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts`. It proves

```
theorem noetherianCharts_of_etaleLocusOpen (hL2 : MurreEtaleLocusOpenStatement.{u, v}) :
    MurreNoetherianChartsStatement.{u, v}
theorem murreChartsFromEtaleLocus : MurreChartsFromEtaleLocusStatement.{u, v}
```

the second being the first restated with the statement of `MurreChartsFromEtaleLocus`. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## The proof

The proof follows Murre's proof of Proposition 2 (Bourbaki exp. 294, printed pp.252–253):
around every point of `F` over a point `s` of the base build a chart from the representing
scheme over the local ring at `s`, make it étale with Lemma 2 and a monomorphism by shrinking.
Murre works over a general locally noetherian base, uses EGA IV 8.8.2 for the shrinking, and
leaves the spreading out to the reader. Here the base is `Spec R`, every chart is affine,
`Spec A[1/b]`, and every shrinking replaces `b` by a multiple; the commutative algebra is in
`MurreChartsAlgebra`.

* `locallyOfFiniteType_ovR`, `formallyUnramified_ovR`: the ring-level properties give those of
  `Spec T ⟶ Spec R` (`HasRingHomProperty.Spec_iff`).
* `exists_good_away`: in the setting of `MurreChartsShrink` (`B = M⁻¹A`, `ξ ∈ F(Spec A)`
  restricting to the element `ξ_B` given by an open immersion `Spec B ⟶ Y_s`), with `A` of
  finite type over `R` noetherian and `B` formally unramified over `R`, and assuming the étale
  loci of the restrictions of `ξ` are open: some `b ∈ M` makes `A[1/b]` formally unramified
  and `resA ξ b` a monomorphism that is infinitesimally étale everywhere. It combines
  `exists_unramified` (giving `m₁`), `exists_etale` and `exists_mono` (applied at `m₁`), with
  `b = m₁ · n_e · n_m`.
* `exists_chart`: let `q : Y ⟶ Spec 𝒪_{Spec R, s}` be formally unramified and locally of finite
  type, `e` a representation of the base change of `F` by `Y`, and `j : Spec B' ⟶ Y` an open
  immersion. Then there is a chart `(U, ξ_U)` with the four properties of
  `MurreNoetherianChartsStatement`, such that every `T` over `Spec R` whose structure morphism
  factors through `Spec 𝒪_s` and every `x' : T ⟶ Y` over `Spec 𝒪_s` with image in the image of
  `j` give an `h : T ⟶ U` with `F(h)(ξ_U) = elemEquiv … x'`. Steps:
  1. `φ : 𝒪_s → B'` with `Spec φ = j ≫ q`; `B'` is an `𝒪_s`-algebra of finite type
     (`LocallyOfFiniteType`), formally unramified over `𝒪_s` and hence over `R`
     (`FormallyUnramified` of `j ≫ q`; `j` is formally unramified because its diagonal is an
     isomorphism). Let `ξ_B = elemEquiv … j`.
  2. Spreading out: `exists_subalgebra_isLocalization` gives `A₀ ⊆ B'` of finite type over `R`
     with `B' = M₀⁻¹A₀`, `M₀` the image of `R \ s`.
  3. (F2), `exists_away_of_isLocalization`: `ξ_B` extends to `ζ ∈ F(Spec A₀[1/a₀])`, `a₀ ∈ M₀`.
     With `A = A₀[1/a₀]` and `M` the image of `M₀`, `B'` is `M⁻¹A`
     (`IsLocalization.isLocalization_of_submonoid_le`).
  4. Lemma 2 (`hL2`) gives the openness of étale loci; `exists_good_away` gives `b`;
     `U = Spec A[1/b]`, `ξ_U = resA ζ b`.
  5. Covering: `x'` factors through `j` (`IsOpenImmersion.lift`), giving `T ⟶ Spec B'`; compose
     with `Spec B' ⟶ Spec A[1/b]` and use `elemEquiv_naturality`.
  The declaration sets `maxHeartbeats` to `1000000` for elaboration time.
* `noetherianCharts_of_etaleLocusOpen`: given the hypotheses of
  `MurreNoetherianChartsStatement`, Lemma 2 applies to every `ovR R T` with `T` of finite type
  and formally unramified over `R` (such `Spec T ⟶ Spec R` is quasi-compact and separated).
  Choose for every `s` the representing scheme `Y_s`; the index type is `Σ s, Y_s` (points of
  `Y_s`), and the chart at `(s, y)` is `exists_chart` for the open immersion of Mathlib's
  `Y_s.affineOpenCover` containing `y`. For a field point `η ∈ F(Spec K)` over
  `f : Spec K ⟶ Spec R`, let `s` be the image of the point; `f` factors through
  `Spec 𝒪_s` (`exists_comp_fromSpecStalk`), `η` corresponds to `x' : Spec K ⟶ Y_s`, and with
  `y` the image of the point the covering property of the chart at `(s, y)` gives the
  factorization.

The modules used, in dependency order: `MurreChartsLocalization`, `MurreChartsAlgebra`,
`MurreChartsLocal`, `MurreChartsAffine`, `MurreChartsEqualizer`, `MurreChartsShrink`,
`MurreChartsMono`, and the statement module `MurreChartsFromEtaleLocus`.

## Sources

J. P. Murre, *Representation of unramified functors. Applications (according to unpublished
results of A. Grothendieck)*, Séminaire Bourbaki exp. 294 (registered as
`murre-1965-bourbaki-294-unramified-functors`), proof of Proposition 2, printed pp.252–253
(PDF pp.11–12). SGA 3, Exposé XI (registered as `sga3-exposes-xi-xii-xiv-gille-polo-2008`),
Remarks 1.6–1.8, for infinitesimal étaleness.
