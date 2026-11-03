# Fixed points at the end of an elementary orbit

Module `Langlands.GroupScheme.ElementaryOrbitLimit`.

## Selected definition

The record's selected declaration is `Langlands.GroupScheme.OrbitLimit.LocalLine k`: the local
ring `k[s]_(s)` of the affine line over the field `k` at the origin, defined as the localization
`Localization.AtPrime (OrbitLimit.originIdeal k)` of the polynomial ring `k[s]` at the prime
ideal `originIdeal k = (s)`. The module proves that it is a discrete valuation ring in which
`OrbitLimit.coord k = s` is irreducible, that evaluation at the origin
`OrbitLimit.evalZero : k[s]_(s) → k` is surjective, and that the residue field is
geometrically reduced over `k`. In the main result it plays the
role of the discrete valuation ring in the valuative extension property that defines
pseudo-completeness. The module's purpose is the theorem below. `LocalLine` is selected
because a definition record has to name a definition.

## Main result

`Langlands.GroupScheme.SchemeAction.exists_isFixed_of_elementary_equivariant`:
let `k` be a field, `H` and `V` group schemes over `Spec k`, and `X` a `k`-scheme with an
action `a : SchemeAction H X`. Assume

- `X` is pseudo-complete (`IsPseudoComplete X`);
- `q : H ⟶ V` is a group scheme morphism and `V` is an elementary quotient
  (`SplitSolvable.IsElementaryQuotient V`): either a one-dimensional vector group
  (`RelativeRoot.IsVectorGroupOfDimension V 1`), or isomorphic to `𝔾_m`;
- `ρ : V.X ⟶ X` is equivariant on every test: for all `T`, `h : T ⟶ H.X` and `v : T ⟶ V.X`,
  `a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ`. So `H` acts on `V` by left translation through `q`.

Then there is a `k`-rational point `y : Over.mk (𝟙 (Spec k)) ⟶ X` that is fixed on every test
(`a.IsFixed y`).

The hypotheses do not include smoothness, connectedness or reducedness of `H`, `V` or `X`.
Nothing is assumed about `q` beyond being a group morphism. Separatedness of `X` comes from
`IsPseudoComplete.isSeparated`.

## Provenance

This is a derived, internal lemma for the proof of
`Langlands.GroupScheme.SplitSolvablePseudoCompleteFixedPointStatement`
(Conrad–Gabber–Prasad, *Pseudo-reductive groups*, Proposition C.1.5). It covers one step of the
induction on a split-solvable series: an orbit through a fixed point of the normal subgroup
descends to an equivariant map out of the elementary quotient `V`. The descent and the
induction are in other modules of the same task. The fact used is the classical one: the closure
of a `𝔾_a`- or `𝔾_m`-orbit in a complete scheme picks up a fixed point at the boundary. The Lean
argument below is a scheme-theoretic version that works on every test. It uses power series and
does not use `ℙ¹`, fixed-point loci or reducedness. CGP's own proof goes another way.

## Proof outline

Write `R = k[s]_(s)` (`OrbitLimit.LocalLine k`), `K = k(s)` (`OrbitLimit.LocalLineFrac k`) and
`s = OrbitLimit.coord k`.

1. **The orbit point over `K`.** Choose a `K`-point `vK` of `V`: in the `𝔾_m` case the point with
   unit coordinate `s`; in the `𝔾_a` case the point with coordinate `1/s`. Pseudo-completeness
   (`IsPseudoComplete.exists_extension`, applied to the discrete valuation ring `R`, whose residue
   field `k` is geometrically reduced) extends `vK ≫ ρ` to `φ : Spec R ⟶ X`. The candidate fixed
   point is `y = φ(s = 0)`, namely `pointOfSpec ≫ specMap evalZero ≫ φ`.

2. **Reduction to affine tests.** By `hom_ext_of_algebraSpec` (an affine open cover argument),
   `a.IsFixed y` reduces to proving `a.act h y_A = y_A` for every `k`-algebra `A` and
   `h : Spec A ⟶ H`, where `y_A` is `y` pulled back to `A`.

3. **The power-series comparison (`OrbitLimit.act_eq_of_laurent`).** Fix `A` and `h`. Suppose
   `w ∈ A⟦X⟧` has zero constant term, becomes a unit in `A⟦X⟧[1/X]`, and satisfies
   `q(h) · vK(X) = vK(w)` as points of `V` over `A⟦X⟧[1/X]` (hypothesis `heq`). Here `vK(t)` is
   `vK` pulled back along `K → A⟦X⟧[1/X]`, `s ↦ t` (`OrbitLimit.laurentPoint`). Compare two
   `A⟦X⟧`-points of `X`: `h · φ(X)` and `φ(w)`, where `φ(t)` is `φ` pulled back along
   `R → A⟦X⟧`, `s ↦ t` (`OrbitLimit.psEval`). Over `A⟦X⟧[1/X]` they agree: by `hρ` the first is
   `(q(h) · vK(X)) ≫ ρ`, and by `heq` this is `vK(w) ≫ ρ`, which is the second. `X` is a
   nonzerodivisor in `A⟦X⟧`, so `A⟦X⟧ → A⟦X⟧[1/X]` is injective (`OrbitLimit.psLoc_injective`).
   Since the scheme `X` is separated, `OrbitLimit.ext_of_injective_appTop` makes the two points agree over
   `A⟦X⟧`: the equalizer is a closed immersion into an affine scheme through which a map with
   injective global sections factors, so it is an isomorphism. Then specialize along the constant
   coefficient map `A⟦X⟧ → A`. Both `X` and `w` go to `0`, so both sides become `y_A`, and this
   gives `a.act h y_A = y_A`.

   `OrbitLimit.exists_isFixed_of_laurent` combines steps 1–3 for any `vK`, assuming a suitable `w`
   exists for every `A` and `h`.

4. **`𝔾_m` case (`OrbitLimit.exists_isFixed_of_gm`).** Through `eV : V ≅ 𝔾_m`, points of `V` over
   `Spec B` are the units of `B` (`OrbitLimit.gmCoord`). This identification is injective,
   multiplicative and natural in `B`, and `OrbitLimit.gmPoint` is a section. If `c ∈ Aˣ` is the
   coordinate of `q(h)`, take `w = c·X`. Then `q(h) · vK(X)` has coordinate `c·X = w`, which is the
   coordinate of `vK(w)`.

5. **`𝔾_a` case (`OrbitLimit.exists_isFixed_of_ga`).** Through the natural additive coordinate
   `e` of a one-dimensional vector group, points over `Spec B` are elements of `B`
   (`OrbitLimit.gaCoord`). This is injective, additive and natural in `B`, and `OrbitLimit.gaPoint`
   is a section. If `c ∈ A` is the coordinate of `q(h)`, then `u = 1 + c·X` is a unit of `A⟦X⟧`;
   take `w = X·u⁻¹`. Then `q(h) · vK(X)` has coordinate `c + 1/X = u/X = 1/w`, the coordinate of
   `vK(w)`. In Lean this identity is a `linear_combination` of the three relations
   `X·(1/X) = 1`, `w·(1/w) = 1` and `u·u⁻¹ = 1` in `A⟦X⟧[1/X]`.

6. **Final theorem.** Split `IsElementaryQuotient V` into the `𝔾_a` and `𝔾_m` cases.

## Declarations

- `OrbitLimit.ext_of_injective_appTop`: two morphisms from an affine `S`-scheme to a separated
  `S`-scheme agree if they agree after a morphism that is injective on global sections.
- Algebra: `originIdeal`, `LocalLine`, `LocalLineFrac`, `coord`, the discrete valuation ring
  instance, `coord_irreducible`, `evalAt` (the `k`-algebra map `s ↦ w`, defined when every
  polynomial with nonzero constant term becomes a unit), `algHom_ext`, `evalZero`,
  `isGeometricallyReduced_residueField`, `fracLift` and `fracLift_comp` (extension to `K` when
  `s` maps to a unit).
- Power series: `constantCoeffAlg`, `psEval` (`s ↦ w` for `w` with zero constant term),
  `PSLoc A = A⟦X⟧[1/X]`, `psLoc`, `psLoc_injective`, `isUnit_psLoc_X`, `laurentPoint` and
  `laurentPoint_coord`.
- Schemes: `specMap` (the relative spectrum of a `k`-algebra map) with `specMap_comp`,
  `specMap_id`, `ΓSpecIso_specMap_appTop` and `specMap_appTop_injective`; `pointOfSpec`,
  `algebraSpec_self_ext`, `hom_ext_of_algebraSpec`, `act_eq_of_laurent`,
  `exists_isFixed_of_laurent`, `gammaIso` (global sections of `algebraSpec k B` are `B`) and
  `algebraMap_coord_ne_zero`.
- Coordinates: `gmCoord`, `gmPoint`, `gmCoord_mul`, `gmCoord_specMap`, `gmCoord_injective`,
  `gmCoord_gmPoint`; `gaCoord`, `gaPoint`, `gaCoord_mul`, `gaCoord_specMap`, `gaCoord_injective`,
  `gaCoord_gaPoint`.
- Cases: `exists_isFixed_of_gm`, `exists_isFixed_of_ga`, and the main theorem
  `SchemeAction.exists_isFixed_of_elementary_equivariant`.

All of these except the main theorem are in the namespace `Langlands.GroupScheme.OrbitLimit`.
