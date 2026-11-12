# The valuative existence criterion for algebraic spaces

Author: Worker 198.

`spaceValuativeExistence` proves `SpaceValuativeExistenceStatement`
(`SpaceValuativeExistenceStatement.lean`), the implication (1) ⇒ (3) of Stacks Project, Lemma
67.42.3 (Tag 0A3Y): let `f : X ⟶ Y` be a quasi-compact, separated, universally closed morphism
of algebraic spaces over a scheme `S`, `A` a valuation ring with fraction field `K`,
`s : Spec A ⟶ S`, `x` a section of `X` over `Spec K` and `y` a section of `Y` over `Spec A` with
`f(x) = y|_K`. Then there is a section `a` of `X` over `Spec A` with `a|_K = x` and `f(a) = y`.
The proof does not use quasi-compactness.

## Source

The statement is Lemma 67.42.3 (Tag 0A3Y) of the chapter *Morphisms of Algebraic Spaces*,
registered source `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, file
`spaces-morphisms.pdf`, printed pp. 90–91. The Stacks proof combines Lemma 67.42.2 (existence
part of the valuative criterion with a field extension) and Lemma 67.41.5 (no extension needed
for separated morphisms). The Lean proof takes a different, direct route: a point of
`X ×_Y Spec A` over the closed point, an étale chart through it, and fppf descent along a
faithfully flat finitely presented `A`-algebra. It uses no field extension.

## Modules

- `ValuativeExistenceAlgebra.lean`: commutative algebra (common denominators in `K ⊗[A] P`,
  flatness of torsion-free modules over a valuation ring, a faithful flatness criterion).
- `ValuativeExistenceTests.lean`: test schemes `Spec R` for `A`-algebras `R`, equalizer ideals
  from separatedness, étaleness of equalizer loci over an étale chart.
- `ValuativeExistenceCore.lean`: the descent step `exists_lift_of_chart`.
- `SpaceValuativeExistenceProof.lean` (this module): the topological part and the final theorem.

## Declarations of this module

- `isOpen_image_chartPointMap` (namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`): an étale
  chart `b : h_V ⟶ F` maps open subsets of `V` to open subsets of `|F|` (point topology
  `pointTopology F`). By `isOpen_pointTopology_iff` one checks the preimage under every étale
  chart `a : h_U ⟶ F`. That preimage is the image of `pr₂⁻¹(O) ⊆ U ×_F V` under the projection
  `pr₁ : U ×_F V ⟶ U` (`chartPointMap_eq_iff_exists_pullback`, `chartPointMap_comm`). The
  projection `pr₁` is étale because `b` is (`IsEtale.projection`), hence an open map.

Namespace `ValuativeExistence`:

- `exists_algHom_eq`: a morphism `Spec R ⟶ Spec Q` of test schemes over `Spec A` is `Spec φ` of
  an `A`-algebra map `φ : Q → R` (`Spec.preimage`).
- `exists_residueField_algHom`: given `g : T ⟶ Spec P` and `h : T ⟶ Spec Q` over `Spec A` and a
  point `τ` of `T`, the residue field `R = κ(τ)` is an `A`-algebra and there are `A`-algebra maps
  `φ : P → R`, `ψ : Q → R` and `e : Spec R ⟶ T` with `e ≫ g = Spec φ`, `e ≫ h = Spec ψ`;
  moreover `φ(p) ≠ 0` whenever `p` is not in the prime `g(τ)` of `P`.
- `exists_algTest_chart`: every point `ζ'` of `|X ×_Y Spec A|` is `chartPointMap (zOf ξ) u'` for
  an `A`-algebra `P`, a section `ξ` of `X` over `Spec P` with `f(ξ) = y|_P` such that
  `zOf ξ : h_{Spec P} ⟶ X ×_Y h_{Spec A}` is étale, and a point `u'` of `Spec P`. Take an atlas
  of `X` (`X.exists_atlas`), the induced étale surjective chart of the base change
  (`SchemePullbackChart.atlas`, `surjective_chartPointMap`), and an affine open of its source
  containing a preimage of `ζ'` (`affineOpenCover`); the composite chart is étale
  (`isEtale_map`, `IsEtale.comp`), and `P` is the coordinate ring with the `A`-algebra structure
  of the second projection.
- `map_snd_chartPointMap`: the image in `|Spec A|` of `chartPointMap (zOf ξ) u` is the point
  `(Spec P → Spec A)(u)`.
- `exists_lift`: the theorem, without the quasi-compactness hypothesis. Let
  `ζ = chartPointMap (zOf x) (closed point of Spec K)` in `|X ×_Y Spec A|`, and `π` the map
  `|X ×_Y Spec A| → |h_{Spec A}|` of the second projection. It is closed by universal
  closedness. So `π(closure {ζ})` is closed. Its preimage under the continuous map
  `schemePoint : Spec A → |h_{Spec A}|` is closed and contains the image of the closed point of
  `Spec K` (it is `π(ζ)`). Every prime of `A` is contained in the maximal ideal, so the closed
  point of `Spec A` lies in the closure of that image (`PrimeSpectrum.le_iff_mem_closure`), hence
  in the closed set. This
  gives `ζ' ∈ closure {ζ}` with `π(ζ')` the closed point. Choose a chart `(P, ξ, u')` through
  `ζ'` (`exists_algTest_chart`). Comparing images in `Spec A` (`schemePointsTo_schemePoint`),
  the prime `v = u'` of `P` lies over the maximal ideal of `A`, so `𝔪_A P ⊆ v`. Now apply
  `exists_lift_of_chart`. Its hypothesis `Htop` is checked as follows. For `p ∉ v` the basic
  open `D(p) ∋ u'` has open image in `|X ×_Y Spec A|` (`isOpen_image_chartPointMap`), which
  contains `ζ'`, hence `ζ`. So some `w ∈ D(p)` has `chartPointMap (zOf ξ) w = ζ`. By
  `chartPointMap_eq_iff_sameImage₂` there are a scheme `T`, morphisms `g : T ⟶ Spec P`,
  `h : T ⟶ Spec K` with `h_g ≫ zOf ξ = h_h ≫ zOf x` and a point `τ` with `g(τ) = w`. Projecting
  to `X` and to `h_{Spec A}` gives `ξ|_g = x|_h` and that `g` and `h` agree over `Spec A`.
  `exists_residueField_algHom` at `τ` gives the field `R = κ(τ)` and maps `k : K → R`,
  `g' : P → R` with `ξ|_{g'} = x|_k` and `g'(p) ≠ 0`, because `p ∉ w`.
- `spaceValuativeExistence`: `SpaceValuativeExistenceStatement.{u}`. It introduces the data and
  applies `exists_lift`; the test scheme `algTest s K` and the morphism `algTestBase s K` are
  by definition the `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)` and
  `Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl` of the statement.

## Checks

`lean_check` of `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof` in
environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lake build) reports no errors or warnings,
and the axioms of `spaceValuativeExistence` are `propext`, `Classical.choice` and `Quot.sound`.
