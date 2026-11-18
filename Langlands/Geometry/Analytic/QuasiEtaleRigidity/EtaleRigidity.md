# Rigidity of étale strong maps over compact analytic domains

Author: Worker 931.

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It proves the
étale case of the uniqueness in Berkovich's Key Lemma 7.2 (*Vanishing cycles
for formal schemes*, 1994, §7). The proof uses the Library's definition of
étale strong maps, `StrongHom.IsEtaleAllPieces`: at every point, `HasAllPiecesAt`
for unramifiedness, in the form of Berkovich's Proposition 3.2.3(b) with finite
pieces. The analytic input is `exists_unramified_rigidity_bound`, not
Berkovich's Krasner-lemma argument.

## Rigid charts

`IsRigidChart g c`, for a strong map `g : ofSaturation A ⟶ ofSaturation B` and a
chart `c`, means the following. There are finitely many functions `F` on `c`
and a bound `δ > 0` such that any two strong maps `x₁ x₂ : S ⟶ ofSaturation A`
satisfying

- `x₁` and `x₂` send a chart `P` of `S` into `c`,
- `x₁ ≫ g = x₂ ≫ g`, and
- at every point, the pullbacks of the functions of `F` along `x₁` and `x₂`
  differ by at most `δ`

have the same pullback `P → c`.

`isRigidChart_of_unramified`: let `V'` be a recognized affinoid subset, let
`f : R → O(V')` be bounded of finite type, and let `e` kill `Ω[O(V')⁄R]`. Let
`c` be a chart inside `V'`, mapped by `g` into a chart `w`, and suppose
`V'.originalRestriction c ∘ f = g.pullback c w ∘ ρ` for some `ρ`. If
`r ≤ |e|` on `c` (in the coordinates of `V'`) for some `r > 0`, then `c` is
rigid.

Proof. Take `G, n, M` from `exists_unramified_rigidity_bound`, let `F` be the
restrictions of `G` to `c`, and let `δ = rⁿ / (2(M·|G| + 1))`. Apply the
algebraic core to `φₖ = xₖ.pullback P c ∘ V'.originalRestriction c`:

- The maps agree on `R`, by the compatibility, `comp_pullback_eq` and
  `x₁ ≫ g = x₂ ≫ g`.
- At a point `x`, `x(φ₁ e)` is the value of `e` at the image point in `V'`
  (`RecognizedSubset.comap_originalRestriction`), hence at least `r`, and
  `M · ∑ ≤ M |G| δ < rⁿ`.

So `φ₁ = φ₂`. The restriction represents a domain
(`RecognizedSubset.originalRestriction_represents`), so `Represents.hom_ext`
cancels it.

## Local covers by rigid charts

`isLocallyChartCovered_isRigidChart`: let `g` be étale and let `D` be an
analytic domain. Every point `y ∈ D` has a neighbourhood whose trace on `D` is
covered by finitely many rigid charts contained in `D`.

Proof. `HasAllPiecesAt` at `y` gives open sets `Vy ∋ y`, `Uy` with `g`
finite from `Vy` over `Uy`. Finitely many charts `w ∋ g y` of the target lie
in `Uy` and cover a neighbourhood of `g y`. For each `w`, let `W` be the
recognized subset of the chart (`originalRecognitionIndex`), and let `V'` be
the finite piece over it from `IsFiniteOver`. Unramifiedness at the point `s`
of `V'` over `y` gives `e` killing the differentials with `s e ≠ 0`. Let `G_w`
be an open set cutting out `{|e| > s e / 2}` on `V'`. Every chart inside
`D ∩ g⁻¹(w) ∩ Vy ∩ G_w` is rigid by `isRigidChart_of_unramified`, applied with
the Library's `originalRestriction_comp_fullRecognitionPairs`. These regions
are locally chart covered (`RefinementGluing`), and together they cover a
neighbourhood of `y` in `D`.

## Main result

`isRigidOn_domainInclusion_comp_etale`: for an étale strong map `g` and a
compact Hausdorff analytic domain `D` of its source, the restriction
`incl_D ≫ map g` is rigid on its whole source. Compactness gives finitely many
rigid charts in `D` covering `D`. The test triples on the domain presentation
are these charts with the functions `F`, bound `δ / 2`, and the chart triple
with function `0`. Given near morphisms over a common composite, merge the
witnesses and compose with the strong inclusion of `D`. The triangle
inequality gives the bound `δ` between `x₁` and `x₂`. The gluing lemma
`localizationFunctor_map_eq_of_local_eq` with `L = D` then applies, and the
inclusion of `D` is cancelled because it is mono.
