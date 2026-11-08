# Forms with `K_ℓ`-coefficients as smooth `GJ_p`-modules and their `Ext` groups (Proposition 4.10)

Author: Worker 61. Built on two modules of Worker 61 that have been
independently accepted but are not yet in the Library (commit 568f1cff):
`Langlands.Shimura.DefiniteFormsSmoothExt` (candidate
`687f402a-30ce-4e91-8e37-a5c30bf357a6`: `awayLevel`, `splitLevel`,
`awayLevelForms`, `mem_awayLevel`, `awayHom_mem_awayLevel`,
`factorHom_mul_awayLevel`, `mem_splitLevel`, `factorHom_mem_splitLevel`,
`awayLevel_le_splitLevel`) and
`Langlands.Cohomology.HyperextAbutmentFunctor` (candidate
`8e1ba75f-07ac-4edf-8a61-c381b99cc033`:
`HyperextAbutment.filtrationFunctor`, `gradedFunctor`, `filtrationι`,
`filtrationMapOfLE`, `gradedπ`). Both are included unchanged in this
candidate's workspace and must be integrated first. It is also built on the
published `Langlands.Shimura.EquivariantForms` (Worker 61: `forms`,
`rightTranslation`),
`Langlands.Shimura.EquivariantFormsHecke` (Worker 61: `transport`),
`Langlands.Shimura.DefiniteFormsDoubleCoset` (Worker 61: `localLevel`,
`ellModuleForms`),
`Langlands.Cohomology.SmoothHyperextSecondPage` (Worker 61:
`SmoothHyperext.secondPageAddEquiv`) and
`Langlands.Cohomology.HyperextSpectralSequence` (Worker 61:
`hyperextSpectralObject`, `hyperextSpectralSequence`, `abutmentIso`); on
Worker 13's published `Langlands.Shimura.SplitLevelTower` (`factorHom`,
`awayHom`, `factorHom_commute_awayHom`, `factorHom_mul_awayHom`),
`Langlands.Shimura.Unitary.PointsSplit` (`DividingPoints`, `PrimeToPoints`,
`finiteAdelicPointsSplit`, `dividingLocalMap_finiteAdelicPointsSplit`),
`Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`) and `Langlands.Cohomology.SmoothExt`
(`SmoothExt.ext`); on Worker 0's published
`Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`
(`smoothPartFixedVectorsEquiv`); and on Worker 57's published
`Langlands.Shimura.Levels` (`CompactOpenLevel` and its arrows) and
`Langlands.Shimura.Unitary.Adelic` (`FiniteAdelicPoints`,
`finiteAdelicDiagonal`, `finiteLocalMap`). From Mathlib it uses
representations and `Rep`, derived categories with their canonical
t-structure (`DerivedCategory.TStructure.t`, `singleFunctor`,
`homologyFunctor`, shifts) and `preadditiveCoyoneda`.

The accepted `DefiniteFormsSmoothExt` treats Harris's Proposition 4.4, whose
coefficients `𝓛` carry the trivial action. This module treats
Proposition 4.10, whose coefficients are a representation `ρ` of `K_ℓ`. The
second argument `𝒜_ℓ(GJ, ρ, H)` of Harris's `E₂` term is constructed as a
smooth representation of `GJ_p`, together with its variation with the level
away from `p`, its `Ext` groups and the published hyperext spectral sequence.
Since the level away from `p` now acts on the coefficients, the levels are
restricted to elements on which the coefficient representation is defined.
Everything is first done for a group `G` with a splitting
`e : G ≃ₜ* H × H'`, a subgroup `D` of `G` and a representation `ρ` of `D`.
It is then specialized to Harris's
`GJ(𝔸_f) ≃ GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`, with `D` the finite adelic
points whose `ℓ`-component lies in `K_ℓ`.

## Conventions

`R` is a commutative ring and `V` an `R`-module. `Γ`, `G`, `H`, `H'` are
groups, `ι : Γ →* G`, and `G`, `H`, `H'` carry topologies.
`e : G ≃ₜ* H × H'` is an isomorphism of topological groups. The published
`factorHom e h = e⁻¹ (h, 1)` and `awayHom e h' = e⁻¹ (1, h')` embed the two
factors in `G`; they commute elementwise, and
`g = e⁻¹ ((e g).1, 1) * e⁻¹ (1, (e g).2)`. The accepted `awayLevel e K'` is
the subgroup `e⁻¹ (1 × K')` of `G`, and `splitLevel e U K'` is
`e⁻¹ (U × K')`.

The published `forms ι K σ`, for a subgroup `K` of `G` and a representation
`σ` of `K` on `V`, consists of the functions `f : G → V` with
`f (ι γ * g) = f g` and `f (g * k) = σ k⁻¹ (f g)` for `k ∈ K`. The published
`rightTranslation` is the representation `(h • f) g = f (g * ψ h)` of a group
`H` on `forms ι K σ`, for `ψ : H →* G` whose image commutes elementwise with
`K`. The published `transport ι σ σ' g hg φ hφ`, for representations `σ` of
`K` on `V` and `σ'` of `L` on `W`, maps `forms ι L σ'` to `forms ι K σ` by
`f ↦ (x ↦ φ (f (x * g)))`, for `g` with `g⁻¹ * k * g ∈ L` for `k ∈ K` and a
linear map `φ : W → V` with `φ (σ' (g⁻¹ * k * g) w) = σ k (φ w)`.

`CompactOpenLevel C` is the published category of compact open subgroups of a
topological group `C`. An arrow `a : K ⟶ L` is an element `a.element = c` of
`C` with `c⁻¹ * k * c ∈ L` for all `k ∈ K` (`a.respects`). A presheaf on
levels is a functor out of `(CompactOpenLevel C)ᵒᵖ`, sending such an arrow to
a map from the value at `L` to the value at `K`. Below `C` is a subgroup of
`H'` with the subspace topology.

`SmoothRep R H` is the published category of smooth representations of a
topological group `H`, `smoothVectors` and `smoothPart` the vectors fixed by
some open subgroup and the representation on them, and
`SmoothRep.smoothPartFunctor : Rep R H ⥤ SmoothRep R H` takes smooth parts.
The published `SmoothExt.ext R H W i : SmoothRep R H ⥤ ModuleCat R` is
`Ext^i(W, -)`, the `i`-th right derived functor of `Hom(W, -)` in smooth
representations, covariant in the second argument.

## Forms with coefficients and right translation by `H`

Namespace `Langlands.Shimura.EquivariantForms`, section `Coefficients`;
universes are arbitrary. Here `D` is a subgroup of `G` and `ρ` a
representation of `D` on `V`.

- `awayPart e : G →* G`: the homomorphism `g ↦ e⁻¹ (1, (e g).2)`
  (`awayPart_apply`). It kills the first factor (`awayPart_factorHom`) and is
  the identity on `awayLevel e K'` (`awayPart_eq_self_of_mem`).
- `coefficientDomain e D`: the subgroup of `H'` of the elements `k` with
  `e⁻¹ (1, k) ∈ D` (the preimage of `D` under `awayHom e`;
  `awayHom_mem_of_mem_coefficientDomain`).
- `domainLevel e K'` (abbreviation): a subgroup `K'` of the coefficient
  domain, viewed as a subgroup of `H'`. `awayLevel_domainLevel_le`:
  `e⁻¹ (1 × K') ≤ D`.
- `coefficientForms R e ι ρ K'` (abbreviation): for a subgroup `K'` of the
  coefficient domain, `forms ι (awayLevel e (domainLevel e K'))` for `ρ`
  restricted to `e⁻¹ (1 × K')`. These are the functions `f : G → V` with
  `f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)` for `k ∈ e⁻¹ (1 × K')`.
- `coefficientTranslation R e ι ρ K'`: the representation of `H` on
  `coefficientForms` by `(h • f) g = f (g * e⁻¹ (h, 1))`, the published
  `rightTranslation` along `factorHom e` (`coefficientTranslation_apply_coe`).
- `coefficientTransport R e ι ρ c hc`, for `c` in the coefficient domain with
  `c⁻¹ * k * c ∈ K₂` for `k ∈ K₁` (`awayHom_conj_mem` transfers this to
  `G`): the `R`-linear map from the forms at `K₂` to the forms at `K₁`,
  `f ↦ (x ↦ ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c))))`. It is the published
  `transport` along `e⁻¹ (1, c)` with intertwiner `ρ (e⁻¹ (1, c))`, which is
  defined because `e⁻¹ (1, c) ∈ D` (`coefficientTransport_apply_coe`).
- `coefficientTransportIntertwining R e ι ρ c hc`: `coefficientTransport` as
  an intertwining map between the `coefficientTranslation` representations,
  since the two factors commute.
- `splitCoefficientHom e U K'`: for a subgroup `U` of `H`, the homomorphism
  `k ↦ e⁻¹ (1, (e k).2)` from `splitLevel e U (domainLevel e K')` to `D`
  (`awayPart_mem_of_mem_splitLevel`, `splitCoefficientHom_apply_coe`).
- `coefficientFixedEquiv R e ι ρ K' U`: the vectors of
  `coefficientTranslation` at `K'` fixed by a subgroup `U` of `H` are
  `R`-linearly equivalent to `forms ι (splitLevel e U (domainLevel e K'))`
  for `ρ ∘ splitCoefficientHom e U K'`, by the identity on functions
  (`coefficientFixedEquiv_apply_coe`). That is, they are the forms of level
  `e⁻¹ (U × K')` on which `k` acts through `ρ (e⁻¹ (1, (e k).2))`. The proof
  writes `k = e⁻¹ ((e k).1, 1) * e⁻¹ (1, (e k).2)`; the first factor acts
  trivially on fixed vectors and the second through `ρ`.
- `isSmoothVector_coefficientTranslation_iff`: a form of level
  `e⁻¹ (1 × K')` with coefficients `ρ` is a smooth vector for
  `coefficientTranslation` if and only if it lies in the right-hand side of
  `coefficientFixedEquiv` for some open subgroup `U` of `H`.
- With `[IsTopologicalGroup H]`: `coefficientSmoothFixedEquiv R e ι ρ K' U`,
  the same description of the vectors of the smooth part fixed by an open
  subgroup `U` of `H` (`smoothPartFixedVectorsEquiv` followed by
  `coefficientFixedEquiv`; `coefficientSmoothFixedEquiv_apply_coe`).
- With `[IsTopologicalGroup H']`: `coefficientFormsPresheaf R e ι ρ :
  (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ Rep R H`, at `K'` the
  representation `coefficientTranslation` at `K'.subgroup`, on an arrow `a`
  the map `coefficientTransportIntertwining` for `a.element`. Functoriality
  uses that `ρ` is a homomorphism on `D`.
- With both: `coefficientSmoothPresheaf R e ι ρ`, the presheaf of smooth
  representations of `H` obtained by following `coefficientFormsPresheaf` with
  `SmoothRep.smoothPartFunctor`.

## `Ext`, the hyperext spectral sequence and its abutment, level by level

Namespace `Langlands.Shimura.EquivariantForms`, section `CoefficientExt`. Here
`R`, `G`, `H` and `V` lie in one universe `u`, as the published smooth `Ext`
requires, and `H`, `H'` are topological groups. Below `A(K')` denotes the
smooth representation `(coefficientSmoothPresheaf R e ι ρ).obj (op K')` for a
compact open level `K'` of the coefficient domain. The letter `n` is a total
degree, not Harris's rank `n`.

- `coefficientExtPresheaf R e ι ρ W i`: for a smooth representation `W` of
  `H` and `i : ℕ`, the presheaf of `R`-modules `K' ↦ Ext^i(W, A(K'))`, that
  is `coefficientSmoothPresheaf` followed by `SmoothExt.ext R H W i`.

With `[HasDerivedCategory.{w} (SmoothRep R H)]` and an object `X` of the
derived category of `SmoothRep R H`:

- `coefficientSpectralSequence R e ι ρ X K'`: the published
  `hyperextSpectralSequence` for the canonical t-structure, of `X` and of
  `A(K')` placed in degree `0` (`(singleFunctor _ 0).obj`).
- `coefficientSecondPageAddEquiv R e ι ρ X K' p q`: the object in position
  `(p, q)` of page 2 is additively equivalent to
  `(coefficientExtPresheaf R e ι ρ (H^{-q}(X)) p).obj (op K')`, that is
  `Ext^p(H^{-q}(X), A(K'))` (the published `secondPageAddEquiv`).
- `coefficientAbutmentPresheaf R e ι ρ X n`: the presheaf of abelian groups
  `K' ↦ Hom(X, A(K')[n])` (`coefficientSmoothPresheaf` followed by
  `singleFunctor _ 0`, the shift by `n` and `preadditiveCoyoneda.obj (op X)`),
  the intended abutment in total degree `n`.
- `coefficientAbutmentIso R e ι ρ X K' n`: the term in degree `n` of the
  published `hyperextSpectralObject` of `X` and `A(K')` at the arrow `⊥ ⟶ ⊤`
  of `EInt` is isomorphic to the value at `K'` of
  `coefficientAbutmentPresheaf X n` (the published `abutmentIso`). This
  identifies a term of the spectral object; it is not a convergence
  statement, and convergence is not proved.
- `coefficientFiltrationPresheaf R e ι ρ X n p` and
  `coefficientGradedPresheaf R e ι ρ X n p`: the step `F^p` of the published
  abutment filtration of `Hom(X, A(K')[n])` and its graded piece
  `gr^p = F^p / F^{p+1}`, as presheaves of abelian groups in `K'`: the
  accepted `HyperextAbutment.filtrationFunctor` and `gradedFunctor` composed
  with `coefficientSmoothPresheaf ⋙ singleFunctor _ 0`.
- `coefficientFiltrationι R e ι ρ X n p : F^p ⟶ abutment`,
  `coefficientFiltrationMapOfLE R e ι ρ X n hpq : F^q ⟶ F^p` for `p ≤ q`, and
  `coefficientGradedπ R e ι ρ X n p : F^p ⟶ gr^p`: the inclusions and the
  projection as natural transformations of presheaves (the accepted
  `filtrationι`, `filtrationMapOfLE` and `gradedπ`, whiskered on the left).

## Harris's case

Namespace `Langlands.Shimura.DefiniteForms`. `A` is a finite-dimensional
`ℚ`-algebra with involution `σ : AlgebraInvolution ℚ A`, `ℓ : FinitePlace ℚ`
a finite place, and `Kℓ` a subgroup of the `ℓ`-adic points
`σ.Points (FiniteCompletion ℚ ℓ)`; no topological condition is imposed on
`Kℓ`. `σ.finiteLocalMap ℓ` is the published `ℓ`-component map `g ↦ g_ℓ` on
`GJ(𝔸_f) = σ.FiniteAdelicPoints`. `𝓛` is a representation of `Kℓ` on an
`R`-module `V`, and `p : ℕ` with `hp : p ≠ 0`. `σ.DividingPoints p` is
`GJ(∏_{v ∣ p} ℚ_v)`, `σ.PrimeToPoints p` is `GJ(𝔸_f^{(p)})`, and
`e = σ.finiteAdelicPointsSplit p hp` is the published splitting
`GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`.

Section `LocalCoefficients` (universes arbitrary except that `A` is in `u`):

- `localCoefficientDomain σ ℓ Kℓ`: the subgroup of `GJ(𝔸_f)` of the `g` with
  `g_ℓ ∈ Kℓ`.
- `localCoefficientMap σ ℓ Kℓ`: the homomorphism `g ↦ g_ℓ` from
  `localCoefficientDomain σ ℓ Kℓ` to `Kℓ` (`localCoefficientMap_apply_coe`).
- `localCoefficientRep σ ℓ Kℓ 𝓛` (abbreviation): `𝓛 ∘ localCoefficientMap`,
  so `g` acts on `V` by `𝓛 (g_ℓ)`.
- `dividingCoefficientDomain σ ℓ Kℓ p hp` (abbreviation): the coefficient
  domain `coefficientDomain e (localCoefficientDomain σ ℓ Kℓ)`, the elements
  `k` of `GJ(𝔸_f^{(p)})` such that the `ℓ`-component of `e⁻¹ (1, k)` lies in
  `Kℓ`.
- `localLevel_awayLevel_le`: for a subgroup `K'` of
  `dividingCoefficientDomain`, the published `localLevel σ ℓ` of
  `e⁻¹ (1 × K')` (the image of its `ℓ`-component map) lies in `Kℓ`.
- `coefficientForms_eq_ellModuleForms` (true by definition): the forms of
  level `e⁻¹ (1 × K')` with coefficients `localCoefficientRep σ ℓ Kℓ 𝓛` are
  the published `ellModuleForms σ ℓ K` (Harris's `𝒜_ℓ(GJ, 𝓛, K)` of (3.7))
  for `K = e⁻¹ (1 × K')` and `𝓛` restricted to `localLevel σ ℓ K`.
- For a place `ℓ` whose prime ideal contains `p` (`hℓ`):
  `finiteLocalMap_awayHom` (the `ℓ`-component of `e⁻¹ (1, k)` is `1`, from the
  published `dividingLocalMap_finiteAdelicPointsSplit`),
  `dividingCoefficientDomain_eq_top`, and
  `coefficientForms_eq_awayLevelForms` (the forms with these coefficients are
  the accepted `awayLevelForms`, the forms with trivial coefficients). This
  case is not Harris's; the definitions do not need `ℓ ∤ p`.

Section `DividingExt`: `R`, `V` and `A` lie in one universe `u`. The
declarations are the generic ones of the previous sections for this `e`,
`ι = σ.finiteAdelicDiagonal` and `ρ = localCoefficientRep σ ℓ Kℓ 𝓛`. Levels
`K'` are compact open levels of `dividingCoefficientDomain σ ℓ Kℓ p hp`.

- `dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp`: the presheaf of smooth
  representations of `GJ(∏_{v ∣ p} ℚ_v)`, at `K'` the smooth part of right
  translation on the forms of level `e⁻¹ (1 × K')` with coefficients
  `𝓛 (g_ℓ)`.
- `dividingCoefficientSmoothFixedEquiv σ ℓ Kℓ 𝓛 p hp K' U`: its vectors at
  `K'` fixed by an open subgroup `U` of `GJ(∏_{v ∣ p} ℚ_v)` are the forms of
  level `e⁻¹ (U × K')` on which `k` acts through `𝓛` of the `ℓ`-component
  of `e⁻¹ (1, (e k).2)`.
- `dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp W i`: `K' ↦ Ext^i(W, A(K'))`
  for a smooth representation `W` of `GJ(∏_{v ∣ p} ℚ_v)`.
- With `[HasDerivedCategory.{w} (SmoothRep R (σ.DividingPoints p))]`:
  `dividingCoefficientSpectralSequence σ ℓ Kℓ 𝓛 p hp X K'`,
  `dividingCoefficientSecondPageAddEquiv … X K' i j` (page 2 in position
  `(i, j)` is `Ext^i(H^{-j}(X), A(K'))`),
  `dividingCoefficientAbutmentPresheaf`, `dividingCoefficientAbutmentIso`,
  `dividingCoefficientFiltrationPresheaf`,
  `dividingCoefficientGradedPresheaf`, `dividingCoefficientFiltrationι`,
  `dividingCoefficientFiltrationMapOfLE` and `dividingCoefficientGradedπ`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4. Worker 61 read the rendered scanned
pages.

- Printed p.310 (one-based PDF page 12): "To continue, we fix a compact open
  subgroup `K_p ⊂ GJ_p` contained in a fixed maximal compact subgroup `C_p`.
  We strengthen (3.6) by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that
  `K^{ℓ,p}` is sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed
  points on `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`. Let `H_p` be an open normal pro-`p`
  subgroup of `C_p` contained in `K_p`, and let
  `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`; when `m = 1` we just write `H`. We now
  assume `𝓛_m` is a module for `K_ℓ/K_ℓ(m)`, as in §3."
- Printed p.311 (one-based PDF page 13): "(4.8)
  `𝒜_ℓ(GJ, 𝓛_m, H(m))^{K_ℓ} ⥲ Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`. The constant étale
  sheaf `𝓛̃_m` on `S(GG, X_{n-1})_{K(N,m)}` descends to a lisse étale sheaf,
  still denoted `𝓛̃_m`, on `S(GG, X_{n-1})_{K(N)}`. The spectral sequence
  (4.4.1) is still `K_{ℓ,m}`-equivariant—though the action is no longer
  trivial—and via (4.8) we obtain a spectral sequence (4.9)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, 𝒪_m(n-1)),
  Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)) ⇒ H^{i+j}(S̄_{K(N)}, 𝓛̃_m)`. Now we want to let
  `m` vary. Let the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
  `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. [...] Proposition 4.10. There is a spectral
  sequence of `𝒪`-modules (4.10.1)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒
  H^{i+j}(S̄_{K(N)}, W̃)`. Here `Ext^i` denotes the `i`-th derived functor of
  `Hom` in the category of smooth `L_ℓ[GJ]`-modules. Moreover, as
  `K(N)^{ℓ,p}`-varies the spectral sequences are `GG(𝔸_f^{ℓ,p})`-equivariant."
- Harris's (3.7) for a representation of `K_ℓ`, which `ellModuleForms`
  formalizes, is quoted in the published `DefiniteFormsDoubleCoset.md`
  (printed p.308): `f(gk) = ρ(k_ℓ)^{-1} f(g)`.

How the module relates to Harris (an explanation, not formalized):

- The second argument. As for Proposition 4.4 in the published
  `DefiniteFormsSmoothExt`, `GJ` acts in (4.10.1) through `GJ_p`, and `Ext`
  is taken among smooth modules. We read `𝒜_ℓ(GJ, ρ, H)` as the functions on
  `GJ(ℚ)\GJ(𝔸_f)` that satisfy (3.7) for the part `K' = K^{ℓ,p} × K_ℓ(1)` of
  `H` away from `p`, with `GJ_p` acting by right translation, and we take the
  smooth part of this action. Harris's level `H` also contains `H_p`. The
  vectors of our module fixed by an open subgroup `U` of `GJ_p` are the forms
  of level `e⁻¹ (U × K')` (`dividingCoefficientSmoothFixedEquiv`). For
  `U = H_p` and `ℓ ∤ p` these are Harris's `𝒜_ℓ(GJ, ρ, H)` at level `H`. That
  last identification needs that elements of `GJ(∏_{v ∣ p} ℚ_v)` have trivial
  `ℓ`-component when `ℓ ∤ p`, which is not formalized here.
- Coefficients. Harris's `(ρ, W)` is, as in §3, a finite-dimensional
  algebraic representation, with `K_ℓ` acting on `W(L_ℓ)` through `ρ`
  (`L_ℓ = L ⊗_ℚ ℚ_ℓ`), and `𝓛 = 𝓛_W` is a `K_ℓ`-stable `𝒪`-lattice in it.
  Here `𝓛` is any representation of any subgroup `Kℓ` of the `ℓ`-adic points
  on any module `V` over any commutative ring `R`; no continuity is required.
  Harris's (4.10.1) is the case `R = L_ℓ`, `V = W(L_ℓ)`; his finite-level
  (4.9) uses `R = 𝒪_m` and `V = 𝓛_m`.
- Levels. We let `K'` range over compact open subgroups of the coefficient
  domain, the elements `k` of `GJ(𝔸_f^{(p)})` whose `e⁻¹ (1, k)` has
  `ℓ`-component in `Kℓ`. Harris's `K^{ℓ,p} × K_ℓ(1)` and
  `K^{ℓ,p} × K_ℓ` are of this form; the product decomposition is not
  formalized and not assumed. The restriction is needed because the arrows
  must act on the coefficients: transport along `c` is
  `f ↦ ρ(c_ℓ) f(· c)`, with `c_ℓ ∈ Kℓ`. When `Kℓ` is open the coefficient
  domain is open in `GJ(𝔸_f^{(p)})`, so its compact open subgroups are those
  of `GJ(𝔸_f^{(p)})` contained in it; this is not formalized.
- Equivariance. We model "as `K(N)^{ℓ,p}`-varies" by presheaves on the
  category of compact open levels of the coefficient domain. Its arrows
  include inclusions of levels and transports by elements of the coefficient
  domain. For `ℓ ∤ p`, elements of `GJ(𝔸_f^{ℓ,p})` have trivial
  `ℓ`-component, so they act by plain right translation; elements with
  `ℓ`-component in `Kℓ` also act on the coefficients (compare Harris's
  remark on p.311 that the `K_{ℓ,m}`-action "is no longer trivial"). The page-2 terms
  (`dividingCoefficientExtPresheaf`), the abutment and its filtration steps
  and graded pieces are such presheaves. The identification of `GG(𝔸_f^{ℓ,p})`
  with `GJ(𝔸_f^{ℓ,p})` that Harris uses is not formalized.
- The first argument. As in `DefiniteFormsSmoothExt`, `M̌_N` and its
  cohomology are not constructed. The spectral sequence takes any object `X`
  of the derived category of smooth representations; Harris's term arises
  when `H^{-j}(X) = H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1))`.
- The abutment and the limit. The spectral sequence is the published hyperext
  spectral sequence, with intended abutment `Hom(X, A(K')[n])`. Neither its
  convergence nor any comparison with `H^{i+j}(S̄_{K(N)}, W̃)` is proved.
  Harris obtains (4.10.1) from the finite-level (4.9) by a Mittag-Leffler
  argument in `m`; we construct the `L_ℓ`-coefficient objects directly and
  formalize neither the limit nor (4.8).
- All declarations are ours, derived from Mathlib and the published modules
  named above. `awayPart`, `coefficientDomain`, `splitCoefficientHom`, the
  generic `coefficient*` declarations and `localCoefficientDomain` are
  internal constructions not printed in Harris 1999.

## Related declarations

- `Langlands.Shimura.EquivariantForms.factorSmoothPresheaf`
  (`Shimura/DefiniteFormsSmoothExt`, accepted, not yet in the Library): the trivial-coefficient case on all
  compact open levels of `H'`. In Harris's case with `ℓ ∣ p`,
  `coefficientForms_eq_awayLevelForms` shows that the forms agree; a general
  comparison of the presheaves is not formalized.
- Library `Langlands.Shimura.EquivariantForms.levelPresheaf`
  (`Shimura/EquivariantFormsHecke`): forms on all compact open levels of `G`
  for a representation of all of `G`, with transports as arrows. Here the
  coefficient representation is defined only on `D`, and the levels and
  arrows lie in the second factor.
- Library `Langlands.Shimura.DefiniteForms.ellModuleForms`
  (`Shimura/DefiniteFormsDoubleCoset`): Harris's `𝒜_ℓ(GJ, 𝓛, K)` at one level;
  `coefficientForms_eq_ellModuleForms` identifies our forms with it at
  `K = e⁻¹ (1 × K')`.

## Scope

The module provides the smooth `GJ_p`-modules of forms with coefficients in a
representation of `K_ℓ`, their variation with the level away from `p`, their
`Ext` groups, the hyperext spectral sequence of any complex `X` against them,
and presheaves of page-2 terms, abutments, filtrations and graded pieces. It
does not:

- construct `M̌_N`, the Shimura varieties or the lisse sheaves `𝓛̃_m`, `W̃`;
- prove (4.5)–(4.9), the Mittag-Leffler argument, convergence, or the
  comparison with the cohomology of `S̄_{K(N)}`;
- assemble the spectral sequences into a presheaf of spectral sequences, or
  prove that `coefficientSecondPageAddEquiv` is natural in `K'`;
- identify the fixed vectors with `ellModuleForms` at `e⁻¹ (U × K')` for
  `ℓ ∤ p`, or treat Hecke operators beyond the arrows of the level category.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published and accepted modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
