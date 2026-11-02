# Local charts of iterated twisting by a line bundle

Internal helper module for the proof of `TwistKillingStatement` (module
`SerreVanishing.Iterate`). It identifies the iterated twists of a module with the module
itself over an open `T` on which the line bundle is trivial. In this identification,
multiplication by a section becomes multiplication by a function.

Throughout, `T : X.Opens`, `L : X.Modules` and
`e : L.restrict T.ι ≅ 𝒪_T` is a trivialization of `L` over `T`. `pullbackTriv T L e`,
`chartMulOf T L e σ` and `SectionClearing.pullbackTensorIso` are the Library constructions
of `LineBundleSectionClearingProof`. `chartMulOf T L e σ` is a morphism `𝒪_X ⟶ L` read as
an endomorphism of `𝒪_T`. `unitEndCoefficient φ ⊤ = φ(1)` is the global function by which
an endomorphism `φ` of `𝒪_T` multiplies.

## Declarations

- `pullback_twistMul_comp`: for `σ : 𝒪_X ⟶ L`, a module `M` and an isomorphism
  `Θ : T.ι^* M ≅ R`, the pullback along `T.ι` of `M ⟶ M ⊗ 𝒪_X ⟶ M ⊗ L` (the inverse right
  unitor followed by `𝟙 ⊗ σ`) is computed as follows. Compose it with the tensor
  comparison `T.ι^*(M ⊗ L) ≅ T.ι^* M ⊗ T.ι^* L`, then with `Θ ⊗ pullbackTriv`, then with
  the right unitor of `R`. The result is `Θ.hom` followed by multiplication by
  `unitEndCoefficient (chartMulOf T L e σ) ⊤`.
- `stripStep T L e Θ`: from `Θ : T.ι^* A ≅ T.ι^* B`, the isomorphism
  `T.ι^*(A ⊗ L) ≅ T.ι^* B`. It is the tensor comparison, then `Θ ⊗ pullbackTriv`, then
  the right unitor.
- `stripIso T L e Z m : T.ι^*((twistIter L m).obj Z) ≅ T.ι^* Z`, defined by recursion on
  `m`: the identity for `m = 0` and `stripStep` of the previous one for `m + 1`.
- `stripIso_succ`: for `s : GlobalSections L`, `T.ι^*((stepNat L s m).app Z)` followed by
  `stripIso (m + 1)` equals `stripIso m` followed by multiplication by
  `unitEndCoefficient (chartMulOf T L e (sectionHom L s)) ⊤`.
- `twistChartIso T L e Z m : ((twistIter L m).obj Z).restrict T.ι ≅ Z.restrict T.ι` is
  `stripIso` conjugated by the Library isomorphism `restrictFunctorIsoPullback T.ι`
  between restriction and pullback.
- `twistChartIso_succ`: the same statement as `stripIso_succ`, for `twistChartIso` and
  the restriction functor.

## Proofs

`pullback_twistMul_comp` combines four Library facts:

- the compatibility of the pullback tensor comparison with the right unitor,
  `pullbackTensorRightUnitor`;
- the naturality of the comparison, `pullbackTensorComparisonApp_naturality`;
- functoriality of `tensorMap`;
- `tensorMap_id_unitEnd` (module `SerreVanishing.Mul`): `𝟙 ⊗ φ` followed by the right
  unitor equals the right unitor followed by multiplication by `φ(1)`.

The remaining step is the naturality of the right unitor. `stripIso_succ` is the special
case `σ = sectionHom L s` and `M = (twistIter L m).obj Z`, because `(stepNat L s m).app Z`
is by definition `twistMul L s ((twistIter L m).obj Z)`. `twistChartIso_succ` follows from
`stripIso_succ` and the naturality of `restrictFunctorIsoPullback`, since multiplication by
a function commutes with every morphism (`Linear.smul_comp`, `Linear.comp_smul`).

## Provenance

Derived for this proof. These are the module-level analogues of the Library charts
`powTriv` and `chartE` of `LineBundleSectionClearingProof`, which treat the powers
`tensorPow L m` themselves. Here the twists `(twistIter L m).obj Z` of an arbitrary module
`Z` are treated. Mathematically this is the standard fact that on `T`, where
`L|_T ≅ 𝒪_T`, multiplication by `s` on `Z ⊗ L^{⊗m}` is multiplication by the local
function representing `s`. That fact is used in the proof of Stacks Project, Lemma 30.17.4
(tag [01XR](https://stacks.math.columbia.edu/tag/01XR)).
