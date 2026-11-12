# Necessity: vanishing of obstruction cohomology at a versal closed point

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Necessity`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`). Everything is proved in the file, with no
hypotheses beyond those in the signatures. Internal construction; no literature statement
is formalized.

## Points

`tr_modIsoR_of_restrict_eq` (generic, for `StackPullback.reindex G F` with a module
realization, as in `PointModule`): if the restriction of a point `x` along `q` is the point
`mkPtR G Rz b ψ` (with `q.left ≫ x.1 = b`), then the transport
`LineBundleFlatDescent.tr (G.map q.left) _ _ (modIsoR G Rz x).hom` equals `ψ.hom`.

## Main theorem

`hOneVanishes_of_isFormallyVersalAt`. Data: `f : X ⟶ Spec R` proper and flat; an
`R`-algebra `P` (noetherian) with an ordered affine cover `K` of `relSpace f P`; a noetherian
`P`-algebra `A₀` with `π = algebraMap P A₀` surjective; `jQ : Q →ₗ[P] P` injective with
range `ker π`; units `g` with `hg` (published `Obstruction`); a derivation
`D : Derivation R P F` which is universal for derivations into `A₀`-modules (`hD`: every
`R`-derivation `δ : P → M` into an `A₀`-module `M` with compatible `P`- and `R`-actions is
`D' ∘ D` for an `A₀`-linear `D' : F → M`); a line bundle `L₀` on `relSpace f A₀` with frames
`e` whose transitions are the reductions of `g`; a field `k` over `R` with a **surjective**
`χ₀ : A₀ →ₐ[R] k` (a closed point of `Spec A₀`). If the family `L₀` is formally versal at
the field point `affineBaseMap χ₀` (`ArtinianChartVersality.IsFormallyVersalAt`), then the
obstruction cone has vanishing first cohomology with coefficients in `k` (an `A₀`-module
through `χ₀`):

`HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap …) (thetaObs f K D g) (zObs …) k`.

### Proof

Let `c ∈ C¹ ⊗ k` and `φ : Q → k` with `d c + φ_* z = 0`. Choose `N` by Artin–Rees
(`NecessityRings.exists_pow_vanish`) and form the Artinian tests `A = ExtRing`,
`B = A₀ / m^N` and the surjection `qE : A → B` (`NecessityRings`); `ι : k → A` is injective
with image `ker qE` and square zero, and `φ` is the obstruction map `phiQ` of this extension
(`algebraMap_jQ`). `exists_deformation` (`NecessityGluing`) gives a line bundle `N` on
`relSpace f A` and an isomorphism `φ_y` from the pullback of `L₀` along `A₀ → B` to the
reduction of `N`, with coordinate `1`. This is a point `y = mkPtR … φ_y` over the test arrow
`qTest` whose residue point is `affineBaseMap χ₀`. Versality
(`ArtinianChartTestReduction.hasLiftingForAt_iff_base`) gives a point `x` over the identity
test of `A` restricting to `y`. Its base map is `affineBaseMap χ'` with `qE ∘ χ' = χN`
(`affineBaseMap_injective`), and its module isomorphism `ψ`, composed with
`pullbackCongr (map_id)`, transports to `φ_y` (`tr_modIsoR_of_restrict_eq`,
`tr_comp_pullbackCongr`). The difference `χ' ∘ π - ρ'` is a derivation
(`exists_derivation_of_lift`), equal to `D'' ∘ D` by `hD`, so `χ' ∘ π = rhoCorr ι … D'' D`.
`exists_b_of_lift` gives `b` with `c = d b + D''_* θ`, and evaluating `χ' ∘ π - ρ'` on
`jQ x` gives `φ + D'' ∘ δ = 0`.
