# Openness of versality on an affine chart

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartOpenness`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`). Everything is proved in the file, with no
hypotheses beyond those in the signatures. Internal construction; no literature
statement is formalized.

## Affine base maps and Artinian tests

- `affineBaseMap_injective`: `affineBaseMap a = affineBaseMap b → a = b`.
- `reduction_comp_affineBaseMap`: for an Artinian test `T` and `χ : A →ₐ[R] T`,
  `reduction T ≫ affineBaseMap χ = affineBaseMap (T.augmentation ∘ χ)`.
- `isUnit_of_reduction`: if `reduction T ≫ affineBaseMap χ = affineBaseMap χ'` for a field
  point `χ' : A →ₐ[R] K'` and `χ' a ≠ 0`, then `χ a` is a unit of the local ring `T`.

## Main theorem

`exists_versal_basicOpen`. Data: `f : X ⟶ Spec R` proper and flat; the chart data of the
published `CechData`/`Obstruction` modules (cover `K` of `relSpace f P`, a noetherian
`P`-algebra `A₀` with `π` surjective, `jQ : Q →ₗ[P] P` injective with range `ker π` and
square-zero products, units `g` with `hg`, a derivation `D : Derivation R P F`, a line
bundle `L₀` on `relSpace f A₀` with frames `e` whose transitions are the reductions of
`g`), with `Q` finite and `F` finite projective over `A₀`, and the lifting property
`hPlift` (for every surjection `q : A → B` of `R`-algebras with square-zero kernel,
every `χ ∘ π` with `χ : A₀ →ₐ[R] B` lifts to `P →ₐ[R] A`). If the obstruction cone has
vanishing first cohomology with coefficients in a field `k` over `A₀`,

`HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap …) (thetaObs …) (zObs …) k`,

then there is `g₀ : A₀` with `algebraMap A₀ k g₀ ≠ 0` such that for every field `K'` over
`R` and every `χ' : A₀ →ₐ[R] K'` with `χ' g₀ ≠ 0`, the family `L₀` is formally versal at
the field point `affineBaseMap χ'` (`ArtinianChartVersality.IsFormallyVersalAt`).

### Proof

Apply the published `ObstructionCone.openStatement` to the complex `cplx f K A₀` (flat:
`flat_cochain`; bounded: `subsingleton_cplx`; finitely generated cohomology:
`finiteCohomology_dif`), with `dθ = δ_* z` (`dif_thetaObs`) and `dz = 0` (`dif_zObs`).
This gives `g₀` and `HOneVanishes` with coefficients in every module over any `A₀`-algebra
in which `g₀` is a unit. For `χ'` with `χ' g₀ ≠ 0`, versality is checked on elementary
surjections `q : A → B` of Artinian tests (`isFormallyVersalAt_iff_elementary`) and on
identity tests (`hasLiftingForAt_iff_base`); `hasBaseLiftingForAt_of_HOneVanishes`
(`BaseLifting`) applies: the kernel of `q` has square zero (`IsElementarySurjection.ker_sq`),
`hPlift` gives the lifts of `P`, and for a chart map `χ : A₀ → B` with residue point
`affineBaseMap χ'`, `χ g₀` is a unit of `B` (`isUnit_of_reduction`), so the openness
conclusion applies to `S = B` (with `A₀ → B` given by `χ`) and every `B`-module `M`.
