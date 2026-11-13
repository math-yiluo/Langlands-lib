# Descent of a valuative lift along a dominating extension: proof

Author: Worker 61.

`spaceValuativeExtensionDescent` proves `SpaceValuativeExtensionDescentStatement`
(`SpaceValuativeExtensionDescentStatement.lean`). This is Stacks Project, *Morphisms of
Algebraic Spaces*, Lemma 67.41.4 (Tag 0ARH). Let `f : X ⟶ Y` be a separated morphism of
algebraic spaces over a scheme `S`. Let `A` be a valuation ring with fraction field `K`,
`s : Spec A ⟶ S`, `x` a section of `X` over `Spec K` and `y` a section of `Y` over `Spec A`
with `f(x) = y|_K`. Assume `HasDominatingValuativeLift f A K s x y`. Then there is a section
`a` of `X` over `Spec A` with `a|_K = x` and `f(a) = y`.

## Source and route

The statement is Lemma 67.41.4 (Tag 0ARH) of the chapter *Morphisms of Algebraic Spaces*,
registered source `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, file
`spaces-morphisms.pdf`, printed pp. 85–86. The Stacks proof reduces to `Y = Spec A`, takes the
scheme-theoretic image of the section `Spec B → X`, and shows that it is `Spec A`.

The Lean proof takes a different route. It reuses the proof of the valuative existence
criterion already in the Library (`SpaceValuativeExistenceProof.lean`,
`ValuativeExistenceCore.lean`). In that proof universal closedness is used only once: it
produces a point `ζ'` of `|X ×_Y Spec A|` in the closure of the point `ζ` given by `x`, lying
over the closed point of `Spec A`. The rest of that proof only uses separatedness. Here the
lift over `B` produces such a point `ζ'` directly, so universal closedness is not needed.

## Notation

`Z = X ×_Y h_{Spec A}` is the base change `ValuativeExistence.baseChange s f y`, with the point
topology `pointTopology Z`. For a section `χ` of `X` over `T` and `t : T ⟶ Spec A` (over `S`)
with `f(χ) = y|_T`, `zOf s f y χ t h : h_T ⟶ Z` is the induced morphism
(`ValuativeExistenceTests.lean`). `chartPointMap (zOf …) : T → |Z|` is its map on points.
`algTest s K` is `Spec K` over `S` and `algTestBase s K : Spec K ⟶ Spec A` is the structure map.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExtensionDescent`:

- `continuous_chartPointMap_zOf`: the map `chartPointMap (zOf s f y χ t h) : T → |Z|` is
  continuous for the Zariski topology on `T` and `pointTopology Z`. Take an atlas `a₀` of `X`
  (`X.exists_atlas`). Base change gives an étale surjective chart of `Z`
  (`SchemePullbackChart.atlas`, `atlas_isEtale`, `atlas_isSurjective`). So
  `Points.map (zOf …)` is continuous (`Points.continuous_map_of_atlas`). The map
  `schemePoint T : T → |h_T|` is continuous (`continuous_schemePoint`). The composite is the
  claim.
- `map_snd_chartPointMap_zOf`: the image of `chartPointMap (zOf s f y χ t h) w` under the
  second projection `|Z| → |h_{Spec A}|` is `schemePoint (t w)`. The proof uses
  `Points.map_comp`, `zOf_snd` and `schemePoint_naturality`.
- `exists_lift_of_mem_closure`: let `ζ = chartPointMap (zOf x) (closed point of Spec K)`. Let
  `ζ'` be a point of `|Z|` in the closure of `{ζ}` whose image in `|h_{Spec A}|` is
  `schemePoint` of the closed point of `Spec A`. If `f` is separated, then there is a section
  `a` over `Spec A` with `a|_K = x` and `f(a) = y`. The proof is the part of
  `ValuativeExistence.exists_lift` (`SpaceValuativeExistenceProof.lean`) after its use of
  universal closedness, with the same steps:
  1. Choose an étale chart `(P, ξ, u')` through `ζ'` (`exists_algTest_chart`).
  2. Comparing images in `Spec A` (`map_snd_chartPointMap`, `schemePointsTo_schemePoint`) shows
     that the prime `v = u'` of `P` lies over the maximal ideal of `A`. So `𝔪_A P ⊆ v`.
  3. Apply `exists_lift_of_chart`. For its topological hypothesis, let `p ∉ v`. The basic open
     `D(p) ∋ u'` has open image in `|Z|` (`isOpen_image_chartPointMap`). This image contains
     `ζ'`, so it meets `{ζ}`. So some `w ∈ D(p)` maps to `ζ`.
  4. By `chartPointMap_eq_iff_sameImage₂` there are a scheme `T`, morphisms `g : T ⟶ Spec P`
     and `h : T ⟶ Spec K` with `h_g ≫ zOf ξ = h_h ≫ zOf x`, and a point `τ` with `g(τ) = w`.
     Projecting to `X` (`zOf_fst`, `map_comp_symm`) gives `ξ|_g = x|_h`. Projecting to
     `h_{Spec A}` (`zOf_snd`) gives `g ≫ algTestBase s P = h ≫ algTestBase s K`.
  5. `exists_residueField_algHom` at `τ` gives a field `R` and `A`-algebra maps `φ : P → R`,
     `ψ : K → R` with `ξ|_φ = x|_ψ` and `φ(p) ≠ 0`, because `p ∉ w`.
- `exists_lift_of_specializes`: a reduction to `exists_lift_of_mem_closure`. The data are:
  - a section `b` of `X` over `T` and `t : T ⟶ Spec A` with `f(b) = y|_T`;
  - morphisms `e_L : T_L ⟶ T` and `e_K : T_L ⟶ Spec K` with `e_L ≫ t = e_K ≫ algTestBase s K`
    and `b|_{e_L} = x|_{e_K}`;
  - a point `w` of `T_L` and a point `m` of `T` with `e_L(w) ⤳ m` and `t(m)` the closed point
    of `Spec A`.

  If `f` is separated, then `x` extends over `Spec A` lying over `y`. Put
  `ζ' = chartPointMap (zOf b t) m`.
  1. The two morphisms `h_{e_L} ≫ zOf b t` and `h_{e_K} ≫ zOf x` agree
     (`pullback.hom_ext`). Their first projections agree by `b|_{e_L} = x|_{e_K}`, their second
     by `e_L ≫ t = e_K ≫ algTestBase s K`.
  2. So `chartPointMap (zOf b t) (e_L w) = chartPointMap (zOf x) (e_K w)` (`chartPointMap_comp`).
     The right side is `ζ`, because `Spec K` has one point (`Subsingleton.elim`).
  3. By continuity (`continuous_chartPointMap_zOf`) the specialization `e_L(w) ⤳ m` gives
     `ζ ⤳ ζ'`, that is, `ζ' ∈ closure {ζ}` (`specializes_iff_mem_closure`).
  4. `map_snd_chartPointMap_zOf` and `t(m) = closed point` give the second hypothesis.

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `spaceValuativeExtensionDescent`: `SpaceValuativeExtensionDescentStatement.{u}`. Unpack the
  dominating lift: a valuation ring `B` with fraction field `L`, a local map `i : A → B`,
  `j : K → L` with `algebraMap B L ∘ i = j ∘ algebraMap A K`, and a section `b` of `X` over
  `Spec B` with `b|_L = x|_L` and `f(b) = y|_B`. Apply `exists_lift_of_specializes` with
  `T = Spec B`, `t = Spec i`, `T_L = Spec L`, `e_L = Spec (algebraMap B L)`, `e_K = Spec j`,
  `w` the closed point of `Spec L` and `m` the closed point of `Spec B`.
  - Every point of `Spec B` specializes to the closed point
    (`IsLocalRing.specializes_closedPoint`).
  - `Spec i` maps the closed point of `Spec B` to the closed point of `Spec A`, because `i` is
    local (`IsLocalRing.comap_closedPoint`).
  - The square `e_L ≫ t = e_K ≫ algTestBase s K` is `Spec` of the ring identity `hij`
    (`Spec.map_comp`, `CommRingCat.ofHom_comp`).

## Scope

The proof uses only `IsSeparatedMorphism f`. It does not use quasi-compactness, universal
closedness, or any hypothesis on the field extension `K → L`. It proves exactly the Library
statement and asserts nothing about the relation between `a` and the section over `B`.
