# Base lifting on an affine chart from vanishing obstruction cohomology

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.BaseLifting`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures. Internal construction; no literature statement is formalized.

This module turns the module-level sufficiency theorem `exists_lift`
(`OpennessOfVersality.Sufficiency`) into the Library's lifting property of actual Picard
points on Artinian tests, `ArtinianChartTestReduction.HasBaseLiftingForAt`, for the
family `L₀` on the affine chart `affineBase R A₀`.

## Helpers

- `exists_affineBaseMap_eq`: every arrow `affineBase R B ⟶ affineBase R A` over
  `Spec R` is `affineBaseMap χ` for an `R`-algebra map `χ : A →ₐ[R] B` (`Spec` is fully
  faithful on rings).
- `tr_comp_pullbackCongr`: for `e : v₁ = v₂`, the transport
  `LineBundleFlatDescent.tr k hu hv₂ (φ ≫ (pullbackCongr e).hom.app D)` equals
  `tr k hu hv₁ φ`.
- `restrict_mkPtR_eq` (generic, for a reindexed pseudofunctor `StackPullback.reindex G F`
  with module realization `Rz`): the restriction along `q : Z' ⟶ Z` of the point
  `mkPtR G Rz a ψ` (base map `a`, module isomorphism `ψ`, see `PointModule`) equals a
  point `y` whenever `q.left ≫ a = y.1` and the transport
  `tr (G.map q.left) _ _ ψ.hom` equals `(modIsoR G Rz y).hom`.

## The kernel of a square-zero surjection

For a surjective ring map `q : A →+* B` whose kernel satisfies `a * b = 0` for all
`a, b ∈ ker q`:

- `isTorsionBySet_ker`: `ker q` is an `A`-module killed by `ker q`;
- `kerModule q hq hsq`: the resulting `B`-module structure on `ker q`, via
  `A ⧸ ker q ≃ B` (`RingHom.quotientKerEquivOfSurjective`);
- `kerModule_smul`: `q a • m = a • m` for `a : A`, `m ∈ ker q`.

## Main theorem

`hasBaseLiftingForAt_of_HOneVanishes`. Data, as in `exists_lift` and the published
`OpennessOfVersality.Obstruction`: `f : X ⟶ Spec R` separated and flat; an `R`-algebra
`P` with an ordered affine cover `K` of `relSpace f P`; a `P`-algebra `A₀` with
`π = algebraMap P A₀` surjective; `jQ : Q →ₗ[P] P` with range `ker π`
(`hjQ`); units `g` on the pairwise intersections of `K` whose coboundary `defect f K g s`
lies in the extension of `ker π` (`hg`); a derivation `D : Derivation R P F`; a line
bundle `L₀` on `relSpace f A₀` with frames `e` on the pieces of `testCover f K A₀`
whose transitions are the reductions of `g` (`hge`). Test data: a field `K'` over `R`, a
residue point `p : residueBase R K' ⟶ affineBase R A₀`, and an arrow of Artinian tests
`q : A ⟶ B` (`ArtinianTest R K'`) such that

- `hq`: `toAlgHom q` is surjective;
- `hsq`: products of two elements of `ker (toAlgHom q)` vanish;
- `hP`: for every `χ : A₀ →ₐ[R] B`, the map `χ ∘ π` lifts to some `ρ : P →ₐ[R] A`,
  i.e. `toAlgHom q ∘ ρ = χ ∘ π`;
- `hH`: for every `χ : A₀ →ₐ[R] B` with `reduction B ≫ affineBaseMap χ = p` and every
  `B`-module `M` whose `A₀`-module structure is the one through `χ`
  (`a • m = χ a • m`), the obstruction cone has vanishing first cohomology
  `HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap …) (thetaObs …) (zObs …) M`.

Conclusion: `ArtinianChartTestReduction.HasBaseLiftingForAt f L₀ p q`, i.e. every point
`y` of the family over the test arrow `baseMap q` (any line bundle `N` on
`relSpace f A`) whose residue map is `p` is the restriction along `q` of a point on the
identity test of `A`.

### Proof

Write `y = ⟨b, ey⟩`, and `b = affineBaseMap χ` (`exists_affineBaseMap_eq`). Choose
`ρ` from `hP`, and give `A` the `P`-algebra structure `ρ`; then `q ∘ ρ = χ ∘ π`
(`hqρ`). Let `M = ker (toAlgHom q)` with its ideal (hence `A`- and `P`-) module structure,
the `B`-module structure `kerModule`, and the `A₀`-module structure through `χ`; the
scalar tower `P → A₀ → M` follows from `kerModule_smul`. The inclusion `jM : M → A` is
`P`-linear and injective with range `ker q` and square-zero products, and `ker q` is
nilpotent since its square is zero. Apply `exists_lift` with the module isomorphism
`modIso f y` of the point (`PointModule`): it gives `χ' : A₀ →ₐ[R] A` with
`q ∘ χ' = χ` and an isomorphism `ψ` from the pullback of `L₀` along `χ'` to `N` whose
transport along `relMap q` is `modIso f y`. The required point is
`mkPtR (relativeSpace f) moduleRealization (affineBaseMap χ') ψ''`, where `ψ''` is `ψ`
followed by the identification of the pullback along `𝟙` with the pullback along
`(relativeSpace f).map 𝟙`. Its restriction is `y` by `restrict_mkPtR_eq`: the base maps
agree by `affineBaseMap_comp` and `q ∘ χ' = χ`, and the transported isomorphism is
`modIso f y` by `tr_comp_pullbackCongr` and the conclusion of `exists_lift`.
