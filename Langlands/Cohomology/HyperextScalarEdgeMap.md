# Edge maps and extension of scalars

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextScalarExtension` (`abutmentMap`,
`cohomologyHomMap`, `IsSemilinear`, the base-change maps and their smooth
specializations; Worker 61), `Langlands.Cohomology.HyperextEdgeMapLinear`
(`HyperextAbutment.edgeMapLinearMap`, `HyperextAbutment.degenerationLinearEquiv`;
Worker 61), `Langlands.Cohomology.HyperextEdgeMap`
(`HyperextEdgeMap.homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso`;
Worker 61), `Langlands.Cohomology.DerivedExactComposition`
(`DerivedPlus.homologyπ_mapHomologyIso_hom`; Worker 727) and
`Langlands.Cohomology.HyperextDegeneration.Proof`
(`hyperextDegenerationStatement_proof`; Worker 894). Through these imports it
also uses `exactDerivedHomologyIso` of
`Langlands.Cohomology.ExactDerivedHomology` (Worker 13),
`mapHomologicalComplexHomologyIso` of
`Langlands.Cohomology.DivisibleSystem.InverseLimit` (Worker 61) and the edge map
`HyperextDegeneration.edgeMap` of
`Langlands.Cohomology.HyperextDegeneration.Statement` (Worker 3).

Let `F : C ⥤ D` be an exact functor of abelian categories, `K` an object of the
derived category of `C`, `W` an object of `C`, `W₀` the complex `W` placed in
degree `0` and `H^q` the cohomology functor in degree `q`. The Library's edge
map `HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`
sends `f` to the map `H^{-n} K → H^0(W₀) ≅ W` induced by `f`. The module
`HyperextScalarExtension` defines comparison maps from the groups attached to
`K`, `W` to those attached to `F K`, `F W`, where `F K` is
`F.mapDerivedCategory.obj K`, and leaves their compatibility with the edge map
open. This module proves that compatibility:

- for every exact `F`, the edge maps commute with `abutmentMap` and
  `cohomologyHomMap`;
- for `F` semilinear along an algebra `R → S`, the edge maps over `R` and over
  `S` intertwine the `S`-linear base-change maps on
  `S ⊗[R] Hom(K, W₀⟦n⟧)` and on `S ⊗[R] Hom(H^{-n} K, W)`;
- when the hyperext degeneration of the Library applies over `R` and over `S`,
  the first base-change map is the second one transported along the
  degeneration isomorphisms, so either is bijective (injective, surjective) if
  and only if the other is;
- under the same hypotheses and an explicit hypothesis that the base-change map
  on `Hom(H^{-n} K, W)` is bijective, the base-change map on abutments is
  packaged as an `S`-linear equivalence (`abutmentBaseChangeLinearEquiv`).

No base-change map is proved to be injective, surjective or bijective.

All declarations are in namespace
`Langlands.Cohomology.HyperextScalarExtension`. Below, `n + a = a'` is the
hypothesis `ha'`, and the following names abbreviate isomorphisms of Mathlib and
the Library.

- `c_q = mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) q`, with
  component `H^q(F L) ≅ F(H^q L)` at a complex `L`.
- `σ`: the components of the shift isomorphisms `H^a(M⟦n⟧) ≅ H^{a'} M`, namely
  `(HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso n a a' ha'`
  for complexes and `(DerivedCategory.homologyFunctor _ 0).shiftIso n a a' ha'`
  in derived categories.
- `φ_L : F(L⟦n⟧) ≅ (F L)⟦n⟧`, the component of
  `(F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n`.
- `ψ_M : Q(M⟦n⟧) ≅ (Q M)⟦n⟧`, the component of `DerivedCategory.Q.commShiftIso n`,
  where `Q` is the localization functor from complexes to the derived category.
- `χ_Y : F(Y⟦n⟧) ≅ (F Y)⟦n⟧`, the component of `F.mapDerivedCategory.commShiftIso n`.
- `h_q = DerivedCategory.homologyFunctorFactors _ q`, with component
  `H^q(Q M) ≅ H^q M` at a complex `M`.
- `μ_L : F(Q L) ≅ Q(F L)`, the component of `F.mapDerivedCategoryFactors`.
- `ε_q = (exactDerivedHomologyIso F q).hom`, with component
  `H^q(F Y) ≅ F(H^q Y)` at an object `Y` of the derived category.

## Complexes

Section `Complexes`: abelian categories `C`, `D` and a functor `F : C ⥤ D` with
`[F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]`; `L` is a
cochain complex in `C` indexed by `ℤ`.

| Declaration | Statement |
| --- | --- |
| `mapHomologicalComplexHomologyIso_shiftIso F n a a' ha' L` | `H^a(φ_L) ≫ σ_{F L} ≫ c_{a'}(L) = c_a(L⟦n⟧) ≫ F.map σ_L`, as maps `H^a(F(L⟦n⟧)) → F(H^{a'} L)`. Tagged `@[reassoc]`. |
| `homologyMap_mapCochainComplexSingleFunctor F W` | `H^0(β'_W) ≫ e_{F W} = c_0(W₀) ≫ F.map e_W`, where `β'_W : F(W₀) ≅ (F W)₀` is the component of Mathlib's `F.mapCochainComplexSingleFunctor 0` and `e_X : H^0(X₀) ≅ X` is Mathlib's `HomologicalComplex.singleObjHomologySelfIso`. |

Proofs.

- `mapHomologicalComplexHomologyIso_shiftIso`: the shift isomorphism of the
  homology functor is the homology of the isomorphism of short complexes
  `CochainComplex.shiftShortComplexFunctorIso`. Composed with the short-complex
  map of `φ_L`, the isomorphism in `D` equals `F` applied to the one in `C`;
  this is checked componentwise (`ext`, `simp` with `Functor.map_units_smul`,
  `HomologicalComplex.XIsoOfEq`, `eqToHom_map`). The statement is then the
  naturality of `ShortComplex.mapHomologyIso` (Mathlib's
  `ShortComplex.mapHomologyIso_hom_naturality`).
- `homologyMap_mapCochainComplexSingleFunctor`: cancel the epimorphism
  `HomologicalComplex.homologyπ` and compute on cycles with Mathlib's
  `homologyπ_naturality`, `homologyπ_singleObjHomologySelfIso_hom`,
  `singleObjCyclesSelfIso_hom`, `cyclesMap_i`,
  `ShortComplex.mapCyclesIso_hom_iCycles`, the Library's
  `DerivedPlus.homologyπ_mapHomologyIso_hom`, and the definition of
  `F.mapCochainComplexSingleFunctor` in degree `0`
  (`HomologicalComplex.singleMapHomologicalComplex_hom_app_self`).

## Cohomology of the derived functor and shifts

Section `Derived` takes an abelian category `C` with
`[HasDerivedCategory.{s} C]`. Section `Exact` takes abelian categories `C`, `D`
with `[HasDerivedCategory.{s} C]`, `[HasDerivedCategory.{s'} D]` and an exact
functor `F : C ⥤ D` as above; `F'` denotes `F.mapDerivedCategory`.

| Declaration | Statement |
| --- | --- |
| `homologyFunctor_map_commShiftIso_shiftIso n a a' ha' M` | For a complex `M` in `C`: `H^a(ψ_M) ≫ σ_{Q M} = h_a(M⟦n⟧) ≫ σ_M ≫ h_{a'}(M)⁻¹`. |
| `exactDerivedHomologyIso_hom_app_Q_obj' F q L` | `ε_q(Q L) = H^q(μ_L) ≫ h_q(F L) ≫ c_q(L) ≫ F.map (h_q(L)⁻¹)`. |
| `mapDerivedCategory_commShiftIso_hom_app_Q_obj F n L` | `F'.map ψ_L ≫ χ_{Q L} ≫ (μ_L)⟦n⟧' = μ_{L⟦n⟧} ≫ Q.map φ_L ≫ ψ_{F L}`. |
| `exactDerivedHomologyIso_shiftIso_Q_obj F n a a' ha' L` | The next statement for `Y = Q L`. |
| `exactDerivedHomologyIso_shiftIso F n a a' ha' Y` | For `Y` in the derived category of `C`: `H^a(χ_Y) ≫ σ_{F' Y} ≫ ε_{a'}(Y) = ε_a(Y⟦n⟧) ≫ F.map σ_Y`. |
| `exactDerivedHomologyIso_shiftMap F f a a' ha'` | For `f : ShiftedHom X Y n`: `H.shiftMap (f.map F') a a' ha' ≫ ε_{a'}(Y) = ε_a(X) ≫ F.map (H.shiftMap f a a' ha')`. Here `H.shiftMap` is Mathlib's `Functor.shiftMap` for `H = DerivedCategory.homologyFunctor _ 0`, the map `H^a X → H^{a'} Y` induced by `f`, and `f.map F'` is Mathlib's `ShiftedHom.map`. |
| `exactDerivedHomologyIso_singleFunctor F W` | `H^0(β_W) ≫ s_{F W} = ε_0(W₀) ≫ F.map s_W`, where `β_W : F'(W₀) ≅ (F W)₀` is the component of Mathlib's `F.mapDerivedCategorySingleFunctor 0` and `s_X : H^0(X₀) ≅ X` is the component of `DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0`. |
| `mapDerivedCategory_homology_isZero F K hK` | If `H^i K` is a zero object, so is `H^i(F' K)`. |

Proofs.

- `homologyFunctor_map_commShiftIso_shiftIso`: Mathlib's
  `DerivedCategory.shiftMap_homologyFunctor_map_Q` for the identity of `M⟦n⟧`,
  after unfolding `Functor.shiftMap` and `ShiftedHom.map`.
- `exactDerivedHomologyIso_hom_app_Q_obj'`: the Library's
  `exactDerivedHomologyIso_hom_app_Q_obj` and the definition of
  `exactDerivedHomologyIsoOnComplexes`.
- `mapDerivedCategory_commShiftIso_hom_app_Q_obj`: Mathlib's
  `NatTrans.shift_app_comm` for `F.mapDerivedCategoryFactors.hom`, which
  commutes with the shifts, and `Functor.commShiftIso_comp_hom_app`.
- `exactDerivedHomologyIso_shiftIso_Q_obj`: precompose both sides with the
  isomorphism `H^a(F'.map ψ_L)`. Both composites are rewritten as the same map
  of complexes: on the left with the previous lemma (solved for `χ_{Q L}`),
  `exactDerivedHomologyIso_hom_app_Q_obj'` in degree `a'`, the naturality of the
  shift isomorphism (`Functor.shiftIso_hom_naturality`) and
  `homologyFunctor_map_commShiftIso_shiftIso` in `D`; on the right with the
  naturality of `exactDerivedHomologyIso` (the Library's
  `exactDerivedHomologyIso_naturality`),
  `homologyFunctor_map_commShiftIso_shiftIso` in `C` and
  `exactDerivedHomologyIso_hom_app_Q_obj'` in degree `a`. The two forms agree by
  the naturality of `h_a` (`DerivedCategory.homologyFunctorFactors_hom_naturality`)
  and `mapHomologicalComplexHomologyIso_shiftIso`.
- `exactDerivedHomologyIso_shiftIso`: both sides are components of natural
  transformations `shiftFunctor n ⋙ F' ⋙ H^a ⟶ H^{a'} ⋙ F`. They agree on every
  object `Q L` by the previous lemma, hence are equal because `Q` is a
  localization functor for the quasi-isomorphisms (Mathlib's
  `Localization.natTrans_ext`).
- `exactDerivedHomologyIso_shiftMap`: by definition `H.shiftMap f a a' ha'` is
  `H^a f` followed by `σ_Y`, and `f.map F'` is `F'.map f ≫ χ_Y`; then
  `exactDerivedHomologyIso_shiftIso` and the naturality of
  `exactDerivedHomologyIso`.
- `exactDerivedHomologyIso_singleFunctor`: the object `W₀` of the derived
  category is `Q` of the complex `W₀`, and `β_W = μ_{W₀} ≫ Q.map β'_W` (Mathlib's
  `Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`).
  The Library's
  `HyperextEdgeMap.homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso`
  identifies `s_X` with `e_X` through `h_0`, in `C` and in `D`. Together with
  `exactDerivedHomologyIso_hom_app_Q_obj'`, the naturality of `h_0` and
  `homologyMap_mapCochainComplexSingleFunctor` this gives the statement.
- `mapDerivedCategory_homology_isZero`: an additive functor preserves zero
  objects (`Functor.map_isZero`), and `ε_i(K)` is an isomorphism
  `H^i(F' K) ≅ F(H^i K)`.

## Edge maps and comparison maps

| Declaration | Statement |
| --- | --- |
| `edgeMap_abutmentMap F K W n f` | For `f : ShiftedHom K W₀ n`: `edgeMap (F' K) (F W) n (abutmentMap F K W n f) = cohomologyHomMap F K W (-n) (edgeMap K W n f)`. |

By the definitions of `HyperextScalarExtension`, `abutmentMap F K W n f` is
`f.map F' ≫ (β_W)⟦n⟧'` and `cohomologyHomMap F K W (-n) g` is
`ε_{-n}(K) ≫ F.map g`. The theorem therefore says that the edge map of the image
of `f` is `H^{-n}(F' K) ≅ F(H^{-n} K)` followed by `F` applied to the edge map of
`f`.

Proof. Unfold `abutmentMap_apply`, `cohomologyHomMap_apply` and the edge map
`H.shiftMap f (-n) 0 _ ≫ s_W`. Mathlib's `Functor.shiftMap_comp` splits the
`shiftMap` of `f.map F' ≫ (β_W)⟦n⟧'` into `H.shiftMap (f.map F')` followed by
`H^0(β_W)`; then `exactDerivedHomologyIso_singleFunctor`,
`exactDerivedHomologyIso_shiftMap` with `a = -n`, `a' = 0`, and `F.map_comp`.

## Extension of scalars

Section `Semilinear`: commutative rings `R : Type uR`, `S : Type uS` with
`[Algebra R S]`, an `R`-linear abelian category `C` with
`[HasDerivedCategory.{s} C]`, an `S`-linear abelian category `D` with
`[HasDerivedCategory.{s'} D]`, an exact functor `F : C ⥤ D` and
`hF : IsSemilinear R S F`. The last six declarations add `[HasExt.{t} C]`,
`[HasExt.{t'} D]` and the hypotheses of the Library's hyperext degeneration
over `R` and over `S`:

- `hK : ∀ i : ℤ, b < i → IsZero (H^i K)` for some `b : ℤ`;
- `hW : ∀ (k : ℤ) (i : ℕ), 0 < i → Subsingleton (Ext^i(H^k K, W))`, with `Ext`
  in `C`;
- `hW' : ∀ (k : ℤ) (i : ℕ), 0 < i → Subsingleton (Ext^i(H^k (F' K), F W))`, with
  `Ext` in `D`.

Here `E_R = degenerationLinearEquiv R (hyperextDegenerationStatement_proof C) K b hK W hW n`
is the edge map `Hom(K, W₀⟦n⟧) ≃ₗ[R] Hom(H^{-n} K, W)`, and `E_S` is the same
equivalence over `S` for `F' K` and `F W`, built with `hW'` and with the
vanishing of `H^i(F' K)` for `i > b` given by `mapDerivedCategory_homology_isZero`.
`E_R.baseChange R S _ _` is Mathlib's `LinearEquiv.baseChange`,
`S ⊗[R] Hom(K, W₀⟦n⟧) ≃ₗ[S] S ⊗[R] Hom(H^{-n} K, W)`.

| Declaration | Statement |
| --- | --- |
| `edgeMapLinearMap_comp_abutmentBaseChangeMap F hF K W n` | `edgeMapLinearMap S (F' K) (F W) n ∘ₗ abutmentBaseChangeMap F hF K W n = cohomologyHomBaseChangeMap F hF K W (-n) ∘ₗ (edgeMapLinearMap R K W n).baseChange S`, as `S`-linear maps `S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(H^{-n}(F' K), F W)`. |
| `edgeMap_abutmentBaseChangeMap F hF K W n x` | The same equation applied to `x : S ⊗[R] Hom(K, W₀⟦n⟧)`. |
| `abutmentBaseChangeMap_eq_degeneration F hF K b hK W hW hW' n` | `abutmentBaseChangeMap F hF K W n = E_S.symm ∘ₗ cohomologyHomBaseChangeMap F hF K W (-n) ∘ₗ E_R.baseChange R S _ _`. |
| `abutmentBaseChangeMap_bijective_iff F hF K b hK W hW hW' n` | `abutmentBaseChangeMap F hF K W n` is bijective if and only if `cohomologyHomBaseChangeMap F hF K W (-n)` is. |
| `abutmentBaseChangeMap_injective_iff`, `abutmentBaseChangeMap_surjective_iff` | The same with injective and with surjective. |
| `abutmentBaseChangeLinearEquiv F hF K b hK W hW hW' n h` | A definition. Given `h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))`, the `S`-linear equivalence `S ⊗[R] Hom(K, W₀⟦n⟧) ≃ₗ[S] Hom(F' K, (F W)₀⟦n⟧)` whose underlying map is `abutmentBaseChangeMap F hF K W n`. |
| `abutmentBaseChangeLinearEquiv_apply F hF K b hK W hW hW' n h x` | `abutmentBaseChangeLinearEquiv F hF K b hK W hW hW' n h x = abutmentBaseChangeMap F hF K W n x`. Tagged `@[simp]`. |

Section `Smooth`: `[Module.Flat R S]`, a topological group `G : Type uG`,
instances `HasDerivedCategory.{s}` on `SmoothRep.{uR, uG, w} R G` and
`HasDerivedCategory.{s'}` on `SmoothRep.{uS, uG, max uS w} S G`, and for the
last two declarations `HasExt.{t}` and `HasExt.{t'}` on these categories. The functor
is `smoothRepExtendScalars.{w} R S G`, `V ↦ S ⊗[R] V`.

| Declaration | Statement |
| --- | --- |
| `smoothEdgeMapLinearMap_comp_abutmentBaseChangeMap R S G K W n` | `edgeMapLinearMap_comp_abutmentBaseChangeMap` for `smoothRepExtendScalars R S G`, with `smoothAbutmentBaseChangeMap` and `smoothCohomologyHomBaseChangeMap`. |
| `smoothAbutmentBaseChangeMap_bijective_iff R S G K b hK W hW hW' n` | `smoothAbutmentBaseChangeMap R S G K W n` is bijective if and only if `smoothCohomologyHomBaseChangeMap R S G K W (-n)` is, under `hK`, `hW` and `hW'` for smooth representations. |
| `smoothAbutmentBaseChangeLinearEquiv R S G K b hK W hW hW' n h` | A definition: `abutmentBaseChangeLinearEquiv` for `smoothRepExtendScalars R S G`. Given `h : Function.Bijective (smoothCohomologyHomBaseChangeMap R S G K W (-n))`, an `S`-linear equivalence `S ⊗[R] Hom(K, W₀⟦n⟧) ≃ₗ[S] Hom(F' K, (F W)₀⟦n⟧)` whose underlying map is `smoothAbutmentBaseChangeMap R S G K W n` (by definition, `rfl`). |

Proofs.

- `edgeMapLinearMap_comp_abutmentBaseChangeMap`: two `S`-linear maps out of
  `S ⊗[R] Hom(K, W₀⟦n⟧)` agree if they agree on pure tensors
  (`TensorProduct.inductionOn`; both sides are additive). On `s ⊗ f` the left
  side is `s • edgeMap (F' K) (F W) n (abutmentMap F K W n f)` and the right side
  is `s • cohomologyHomMap F K W (-n) (edgeMap K W n f)` (the `_tmul` lemmas of
  `HyperextScalarExtension`, `LinearMap.baseChange_tmul` and
  `LinearMap.map_smul`); they are equal by `edgeMap_abutmentMap`.
- `edgeMap_abutmentBaseChangeMap`: `LinearMap.congr_fun`.
- `abutmentBaseChangeMap_eq_degeneration`: `E_S` is the edge map over `S` by
  definition, so the equation at `x` is `edgeMap_abutmentBaseChangeMap`
  rearranged with `LinearEquiv.eq_symm_apply`.
- The three `iff` statements: rewrite with
  `abutmentBaseChangeMap_eq_degeneration`; composing with the equivalences
  `E_S.symm` and `E_R.baseChange` preserves and reflects bijectivity,
  injectivity and surjectivity (Mathlib's `EquivLike.comp_bijective`,
  `EquivLike.bijective_comp` and their injective and surjective versions).
- `abutmentBaseChangeLinearEquiv`: Mathlib's `LinearEquiv.ofBijective` applied
  to `abutmentBaseChangeMap F hF K W n`, whose bijectivity is
  `(abutmentBaseChangeMap_bijective_iff F hF K b hK W hW hW' n).2 h`.
  `abutmentBaseChangeLinearEquiv_apply` holds by `rfl`.
- The smooth statements are the general ones for
  `smoothRepExtendScalars R S G`, which is exact by the instances of
  `HyperextScalarExtension` and semilinear by
  `smoothRepExtendScalars_isSemilinear`.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
Worker 13, the first executor of the task, asked Worker 61 for the change of
coefficients from `𝒪` to `L_ℓ` and for the maps it induces on the degeneration
of Harris's spectral sequence. The Library's `HyperextScalarExtension`
supplies the comparison maps; this module supplies their compatibility with the
edge maps and hence with the degeneration isomorphisms.

For this module Worker 61 read the following passages of Harris 1999, in the
rendered scans (the text layer of this scan is unreliable):

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §4, printed p.311 (one-based PDF page 13), Proposition 4.10: "There is a
  spectral sequence of `𝒪`-modules (4.10.1)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, L_ℓ(n - 1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`."
  `Ext^i` is taken in the category of smooth `L_ℓ[GJ]`-modules; `𝒪` is the ring
  of integers of `L_ℓ` (printed p.307, one-based PDF page 9).
- §4-§5, printed p.312 (one-based PDF page 14): "In fact, we have proved the
  stronger (integral) statement (4.10.4)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒ H^{i+j}(S̄_{K(N)}, 𝓛̃)`."
  Later on the same page: "since `π_v` is supercuspidal, the higher Ext's
  vanish and the spectral sequence (4.10.1) degenerates to an isomorphism
  (5.2)
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`".

Interpretation (explanation only). The Library models the degeneration of a
hyperext spectral sequence when the higher `Ext` groups vanish through the edge
map `HyperextDegeneration.edgeMap`, which is bijective under the hypotheses
`hK`, `hW` (`hyperextDegenerationStatement_proof`). Harris's spectral sequence
exists with integral coefficients (4.10.4) and with `L_ℓ`-coefficients
(4.10.1), and (5.2) uses the integral cohomology `H_c(M̆_N, 𝒪(n - 1))`
together with the `L_ℓ`-module `𝒜_ℓ(GJ, ρ, H)[π^v]`. With `R = 𝒪`, `S = L_ℓ`
and extension of scalars as `F`, this module shows that the edge maps over
`𝒪` and over `L_ℓ` are compatible with extension of scalars, and that when both
degenerate the comparison map `L_ℓ ⊗_𝒪 Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)` on
abutments is bijective exactly when the comparison map on
`Hom(H^{-n} K, W)` is. The formalization does not identify Harris's objects
with `K`, `W`, `F K`, `F W`, and does not decide whether the comparison maps
are bijective in Harris's situation.

## Scope

- No base-change map is proved to be injective, surjective or bijective; the
  `iff` statements only transfer these properties between the map on
  abutments and the map on `Hom` out of cohomology.
- `abutmentBaseChangeLinearEquiv` and `smoothAbutmentBaseChangeLinearEquiv`
  take the bijectivity of the base-change map on `Hom(H^{-n} K, W)` as the
  explicit hypothesis `h`, which is not established here. The Markdown file
  of `Langlands.Cohomology.HyperextScalarExtension` gives an example, as explanation only, where a
  base-change map of this kind is not surjective.
- The vanishing of higher `Ext` over `S` (`hW'`) is a separate hypothesis; it is
  not deduced from the vanishing over `R` (`hW`).
- Group actions, the Hecke and `Z_v` actions of Harris and isotypic parts are
  not treated. In particular, no statement relates the isotypic parts of a
  representation over `R` to those of its extension of scalars to `S`; this
  remains an open obligation.
- The geometric inputs of Proposition 4.10 and the identifications needed to
  apply the module to Harris's (4.10.1), (4.10.4) and (5.2) are not formalized;
  Worker 13 lists them as planned obligations.
- `HasExt` and `HasDerivedCategory` are hypotheses; the results hold for each
  such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.307, 311 and 312 (rendered scans) read for this module.

Dependencies: `Langlands.Cohomology.HyperextScalarExtension`,
`Langlands.Cohomology.HyperextEdgeMapLinear`,
`Langlands.Cohomology.HyperextEdgeMap`,
`Langlands.Cohomology.DerivedExactComposition` and
`Langlands.Cohomology.HyperextDegeneration.Proof`, with Mathlib pinned to Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
