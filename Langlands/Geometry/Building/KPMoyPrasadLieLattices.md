# The Lie lattices `𝔤_{x,r} = Lie(𝒢_{x,r})` and their `LieFiltrationData`

Let `F` be a nonarchimedean local field of either characteristic, `G` an affine group over `F`
and `P : ParahoricBuildingData G`, with maximal split torus `S`, centralizer `Z = Z_G(S)` and
apartment `A(S)`. KP §13.3.1 defines the Moy–Prasad lattice `𝔤_{x,r}` as the Lie algebra of the
smooth model `𝒢_{x,r}` attached in §8.5 and §9.8.2 to the constant concave function `r`, and KP
13.3.3 describes it as the `𝒪`-span of the Lie algebra `𝔷_r` of the model `𝒵_r` of `Z` and of
the Lie algebras `𝔲_ψ` of the root models `𝒰_ψ` of KP 9.4.5, `ψ(x) ≥ r`. The Library's
`ParahoricBuildingData.LieFiltrationData` (`KPLieFiltration`) takes `𝔷_r` and `𝔲_ψ` as data. This
module constructs these lattices from models chosen from the existence statements of
`KPMoyPrasadModelStatements`, which enter as explicit hypotheses, and assembles them into an
actual `P.LieFiltrationData`, to which the real-depth, strict-depth, dual, building and graded
constructions of `KPLieFiltrationDual`, `KPLieFiltrationOnBuilding` and `KPLieGradedPairing`
apply.

Lie lattices are `IntegralModel.lieLattice`: the image of the injective `𝒪[F]`-linear map
`Lie(𝒢) → Lie(G)` (`IntegralModel.LieLattice`), an `𝒪[F]`-submodule of `GenericLie 𝒪[F] G`.

## Lie lattices and maximal-unramified points

- `IntegralModel.Hom.lieLattice_le_of_id`: a homomorphism of models extending the identity of
  the generic group gives `Lie(M) ⊆ Lie(N)`. It is `Hom.map_lieLattice_le` with
  `GenericLie.map_id`.
- `IntegralModel.lieLattice_le_of_unramified`: for a smooth model `M` of `G` over `𝒪[F]` and
  any model `N`, if the integral points of `M` over the integers of the maximal unramified
  extension `K = inertiaFixedField F` lie in those of `N`, then `Lie(M) ⊆ Lie(N)`. The proof
  extends the identity of `G` to a homomorphism `M → N` by `unramifiedSmoothHomExtension`
  (KP Corollary 2.10.10 tested on points over the integers of `K`) and applies the previous
  lemma.
- `IntegralModel.lieLattice_eq_of_unramified`: two smooth models with the same integral points
  over the integers of `K` have the same Lie lattice (KP Corollary 2.10.11). Points over
  `𝒪[F]` would not suffice; `KPMoyPrasadModelStatements` gives an example.
- `RelativeRoot.map_mem_of_hasLieImage`: if `j : U ⟶ G` represents a subgroup functor whose
  tangent image is `W` (`HasLieImage`), the differential of `j` takes values in `W`: the
  dual-number point of `G` given by `j` composed with a tangent vector of `U` factors through
  `j`, hence lies in the subgroup functor.

## The chosen lift and the models

- `unramifiedApartmentLift P`: a special torus containing `S` with an apartment lift to `K`,
  chosen by `Classical.choice` from `exists_unramifiedApartmentLift` applied to the published
  theorems `specialTorusExistence` and `unramifiedValuationDescent`, as
  `centralizerUnramifiedApartmentLift` does for the centralizer building.
- `moyPrasadModel hG hP h x r`: the model `𝒢_{x,r}` over `𝒪[F]` chosen from
  `hG : MoyPrasadModelStatement` for the chosen lift, with `hP : P.SatisfiesApartmentAxioms` and
  `h : P.MinimalCongruentCentralizerOrder`. Its specification: `moyPrasadModel_isSmooth`,
  `moyPrasadModel_hasGeometricallyConnectedFibres`, `moyPrasadModel_unramifiedIntegralPoints`
  (points over the integers of `K` are `G(K)_{x,r}`) and `moyPrasadModel_integralPoints`
  (points over `𝒪[F]` are `P_{x,r}`).
- `centralizerModel hZ r`: the model `𝒵_r` of `Z` chosen from `hZ : CentralizerModelStatement`,
  with `centralizerModel_isSmooth`, `centralizerModel_unramifiedIntegralPoints` (`Z(K)_{x₀,r}`)
  and `centralizerModel_integralPoints` (`Z(F)_r`).
- `rootGroupScheme α` and `rootGroupInclusion α`: a representative `U_a ⟶ G` of the root
  subgroup functor of the relative root `a = α`, chosen from the published theorem
  `RelativeRoot.rootSubgroupRealization`; it is a closed subgroup
  (`rootGroupInclusion_isClosedSubgroup`, which gives the instance
  `rootGroupScheme_isAffineHom`) whose tangent image is the span of the weight spaces
  `𝔤_{na}`, `n ≥ 1` (`rootGroupInclusion_hasLieImage`).
- `affineRootDerivative ψ`: the relative root `a` with `ψ.linear = rootForm a`, chosen from the
  definition of `P.affineRoots`; it is unique (`eq_affineRootDerivative`, from
  `rootForm_injective_of_split`, since `S` is split).
- `affineRootModel hU hP ψ`: the model `𝒰_ψ` of `U_a`, `a = affineRootDerivative ψ`, chosen from
  `hU : AffineRootGroupModelStatement`, with `affineRootModel_isSmooth` and
  `affineRootModel_integralPoints` (image `U_ψ` in `G(F)`).

## The lattices

- `moyPrasadLie hG hP h x r = Lie(𝒢_{x,r})`, the lattice `𝔤_{x,r}` of KP §13.3.1; it is an
  `𝒪[F]`-lattice in `Lie(G)` (`moyPrasadLie_isLattice`, from `lieLattice_isLattice`).
- `moyPrasadLiePlus hG hP h x r = ⨆_{s > r} 𝔤_{x,s}`, the lattice `𝔤_{x,r+}` of KP §13.3.1
  (strict-depth convention of KP §1.6); `moyPrasadLie_le_moyPrasadLiePlus`.
- `centralizerModelLie hZ r = Lie(𝒵_r) ⊆ Lie(Z)`, the lattice `𝔷_r` of KP 13.3.3.
  `centralizerModelLie_antitone` proves that it decreases in `r`, given
  `MinimalCongruentOrderStatement`: the minimal congruent torus filtration decreases, hence so
  does `Z(K)_{x₀,r}` (`moyPrasadWith_antitone`), and `lieLattice_le_of_unramified` applies to
  the models `𝒵_s → 𝒵_r`.
- `affineRootModelLie hU hP ψ`, the lattice `𝔲_ψ ⊆ Lie(G)` of KP 13.3.3: the image of
  `Lie(𝒰_ψ)` under the differential of `rootGroupInclusion a`. It does not depend on the
  representative of the root subgroup. `affineRootModelLie_le_rootLieSpace` proves
  `𝔲_ψ ⊆ Lie(U_a) = P.rootLieSpace a` by `map_mem_of_hasLieImage`.

## The `LieFiltrationData`

`lieFiltrationData hZ hU hOrder hP : P.LieFiltrationData` has `centralizerLie r = Lie(𝒵_r)`
(`lieFiltrationData_centralizerLie`) and `affineRootLie ψ = Lie(𝒰_ψ)` mapped into `Lie(G)`
(`lieFiltrationData_affineRootLie`); its two proof fields are `centralizerModelLie_antitone` and
`affineRootModelLie_le_rootLieSpace`. Its `lieFiltration x r` is the `𝒪[F]`-span of the image
of `Lie(𝒵_r)` and of the `Lie(𝒰_ψ)` with `ψ(x) ≥ r`. KP §13.3.3 identifies this span with
`𝔤_{x,r}` (here `moyPrasadLie x r`), and KP §13.3.1 gives its periodicity
`𝔤_{x,r+1} = 𝔪 𝔤_{x,r}`; neither is proved in this module. The lemma
`IntegralModel.lieLattice_eq_of_unramified` gives independence of the choices: smooth models of
the same generic group with the same integral points over the integers of `K` have the same Lie
lattice.

The hypotheses `hG`, `hZ`, `hU` (`MoyPrasadModelStatement`, `CentralizerModelStatement`,
`AffineRootGroupModelStatement` of `KPMoyPrasadModelStatements`) and `hOrder`
(`MinimalCongruentOrderStatement` of `TorusFiltration.StructuralStatements`) are Prop-valued
statements; this module does not prove them.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (printed page = PDF
  page − 31): Corollaries 2.10.10–2.10.11 (p. 124); Fact 2.10.16 (p. 126); §8.5 and 8.5.20
  (pp. 310–320); 9.4.5 and Lemma 9.4.6 (pp. 347–348); §9.8.2 and Proposition 9.8.3
  (pp. 375–376); §13.3.1 and §13.3.3 (pp. 470–471); Definition B.10.8 (p. 690).
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. There is no entry for
  9.4.5, §9.8.2 or §13.3.
