# Descent of the building quotient from the maximal unramified extension

`Langlands.Geometry.Building.UnramifiedBuildingDescentStatement` is a
proposition. Nothing in this module proves it.

## The statement

The proposition is universe polymorphic. At each universe `u` it ranges over
every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, in equal and mixed characteristic, every
actual group scheme `G` over `Spec F` with a proof
`hG : IsConnectedReductive G`, and every `B : ValuationBuildingData G`. The
instance `IsAffineHom G.X.hom` is derived from `hG`; it is not a premise.
No building axiom is assumed of `B`.

Write `L = inertiaFixedField F` for the actual maximal unramified extension
(the Library's separable inertia fixed field, definitionally
`UnramifiedClosure F`) and `G_L = baseChanged F L G` for the actual scalar
extension. The conclusion asserts that there exist:

* `C : MaximalUnramified.BuildingData F G_L`: building data over `L` for its
  constructed integer-valued valuation `MaximalUnramified.valuation F`, with
  its existing reduced quotient (7.6.2) and rational-point action;
* `D : MaximalUnramified.SemilinearApartmentData C`: an action of the group of
  `F`-automorphisms of `L` on the apartment of `C`, compatible with the actual
  coefficient conjugation of rational points on the normalizer and on the
  zero-depth root filtrations. Its quotient action `D.action` is the
  published semilinear action on `C.ReducedBuilding`;
* a map `e : B.ReducedBuilding → C.ReducedBuilding`,

such that

1. `e` is injective;
2. `e` is equivariant along the actual scalar extension of rational points:
   `e (g • z) = rationalExtend F L G g • e z` for every `g : rationalPoints G`;
3. every point `y` of `C.ReducedBuilding` fixed by `D.action σ` for every
   `σ : L ≃ₐ[F] L` is `e z` for some `z`;
4. if `e z` is a special point of `C`, then `z` is a special point of `B`.

## Source correspondence

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

* §9.2.1, printed pp. 325–326 / PDF pp. 356–357, defines the action of
  `Γ = Gal(K/k)` on `B(G_K)` for `K` the maximal unramified extension, through
  coefficient conjugation, and the `G(k)`-equivariant embedding of the fixed
  locus. §9.2.3, printed p. 326 / PDF p. 357, defines `B = B(G_K)^Γ` and
  observes that special `k`-apartments are `Γ`-stable. Theorem 9.2.7, printed
  p. 329 / PDF p. 360, shows that `B` is the building of `G(k)`.
* Theorem 9.6.5 and §9.6.6, printed pp. 366–367 / PDF pp. 397–398, identify
  `B(G_K)^Γ` `G(k)`-equivariantly with the Chapter 7 valuation quotient built
  from the valuation of the root datum of Theorem 9.6.5.
* Proposition 9.9.2, printed p. 380 / PDF p. 411: a point of `B(G)` that is
  special in `B(G_K)` is special in `B(G)`.

Composing the bijection of §9.6.6 with the inclusion of `B(G_K)^Γ` into
`B(G_K)` gives `e`, clauses 1 and 2, and clause 3 for the Galois action of
§9.2.1. Proposition 9.9.2 gives clause 4. The upstairs data `C` and `D` are
taken on a special `k`-apartment, whose torus is defined over `k`, so that the
Galois action preserves the apartment as `SemilinearApartmentData` requires.

The statement quantifies over every `B`, not only the datum constructed in
Chapter 9. The apartment class of `B` is `ω`-compatible, and Kaletha–Prasad
Proposition 6.2.6, printed p. 216 / PDF p. 247 (proved in the Library as
`omegaCompatibleApartmentUniqueness`), shows that such a class is unique for a
given maximal split torus and centralizer datum. Any two maximal split tori are
`G(F)`-conjugate (the Library's `smoothMaximalSplitTorusConjugacy`). So the
quotient of every `B` is the Bruhat–Tits building of `G`, and the cited
assertions apply to it.

The provenance is derived: the statement combines the cited assertions on the
Library's existing quotients, actions and Galois data. The existential form
lets a proof choose the upstairs datum and Galois action. A consumer can use
clause 3 for every admissible `D`: the published
`unramifiedIntegralImage_semilinearAction_eq_of_unique_fixed` shows that a
point uniquely fixed by an extended integral image is `D.action`-fixed.

## Scope

This is a statement. It does not construct `C`, `D` or `e`, and it asserts no
metric, building axiom, stabilizer identity or integral-model property.
