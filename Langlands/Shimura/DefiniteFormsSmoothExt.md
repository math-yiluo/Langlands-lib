# Harris's smooth `GJ_p`-modules of forms and their `Ext` groups (Proposition 4.4)

Author: Worker 61. Built on the published `Langlands.Shimura.EquivariantForms`
(Worker 61: `forms`, `rightTranslation`),
`Langlands.Cohomology.SmoothHyperextSecondPage` (Worker 61:
`SmoothHyperext.secondPageAddEquiv`),
`Langlands.Cohomology.HyperextSpectralSequence` (Worker 61:
`hyperextSpectralObject`, `hyperextSpectralSequence`, `abutmentIso`),
`Langlands.Cohomology.HyperextAbutmentFiltration` and
`Langlands.Cohomology.HyperextAbutmentNaturality` (Worker 61:
`HyperextAbutment.filtration`, `graded`, `filtrationPostcomp`,
`gradedPostcomp` and their `_id`/`_comp` lemmas); on Worker 13's published
`Langlands.Shimura.SplitLevelTower` (`factorHom`, `awayHom`,
`factorHom_commute_awayHom`, `factorHom_mul_awayHom`),
`Langlands.Shimura.PartialLevelTower` (`CompactOpenLevel.prod`),
`Langlands.Shimura.Unitary.PointsSplit` (`DividingPoints`, `PrimeToPoints`,
`finiteAdelicPointsSplit`),
`Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`) and `Langlands.Cohomology.SmoothExt`
(`SmoothExt.ext`); on Worker 0's published
`Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`
(`smoothPartFixedVectorsEquiv`); and on Worker 57's published
`Langlands.Shimura.Levels` (`CompactOpenLevel` and its arrows),
`Langlands.Shimura.PEL.TraceSimilitudesLevels` (`CompactOpenLevel.transport`)
and `Langlands.Shimura.Unitary.Adelic` (`FiniteAdelicPoints`,
`finiteAdelicDiagonal`). From Mathlib it uses representations and `Rep`,
derived categories with their canonical t-structure
(`DerivedCategory.TStructure.t`, `singleFunctor`, `homologyFunctor`, shifts)
and `preadditiveCoyoneda`.

The module constructs the second argument `𝒜_ℓ(GJ, 𝓛, K(m))` of Harris's
`E₂` term in Proposition 4.4 as a smooth representation of the local group
`GJ_p`, for trivial coefficients `𝓛`, and its variation with the level away
from `p`. It then applies the published hyperext spectral sequence and smooth
`Ext` groups to it. Everything is first done for a group `G` with a given
splitting `e : G ≃ₜ* H × H'`, then specialized to Harris's
`GJ(𝔸_f) ≃ GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`.

## Conventions

`R` is a commutative ring, `V` an `R`-module, and `Representation.trivial`
is the trivial action on `V`. `Γ`, `G`, `H`, `H'` are groups, `ι : Γ →* G`,
and `G`, `H`, `H'` carry topologies. `e : G ≃ₜ* H × H'` is an isomorphism of
topological groups. The published `factorHom e h = e⁻¹ (h, 1)` and
`awayHom e h' = e⁻¹ (1, h')` embed the two factors in `G`. The published
`forms ι K ρ`, for a subgroup `K` of `G` and a representation `ρ` of `K` on
`V`, consists of the functions `f : G → V` with `f (ι γ * g) = f g` and
`f (g * k) = ρ k⁻¹ (f g)`; for `ρ` trivial the second condition is
`f (g * k) = f g`. The published `rightTranslation ι K ρ ψ hψ` is the
representation `(h • f) g = f (g * ψ h)` of a group `H` on `forms ι K ρ` for
`ψ : H →* G` whose image commutes elementwise with `K`.

`CompactOpenLevel H'` is the published category of compact open subgroups of
`H'`. An arrow `a : K ⟶ L` is an element `a.element = g` of `H'` with
`g⁻¹ * k * g ∈ L` for all `k ∈ K` (`a.respects`). A presheaf on levels is a
functor out of `(CompactOpenLevel H')ᵒᵖ`, sending such an arrow to a map from
the value at `L` to the value at `K`.

`SmoothRep R H` is the published category of smooth representations of a
topological group `H`. `smoothVectors ρ` and `smoothPart ρ` are the vectors
fixed by some open subgroup and the representation on them. The published
`SmoothRep.smoothPartFunctor : Rep R H ⥤ SmoothRep R H` takes smooth parts.
The published `SmoothExt.ext R H W i : SmoothRep R H ⥤ ModuleCat R` is
`Ext^i(W, -)`, the `i`-th right derived functor of `Hom(W, -)` in smooth
representations, covariant in the second argument.

## Forms of level `e⁻¹ (1 × K')` and right translation by `H`

Namespace `Langlands.Shimura.EquivariantForms`, section `Split`; universes are
arbitrary.

- `awayLevel e K'`: the subgroup `e⁻¹ (1 × K')` of `G` (the image of `K'`
  under `awayHom e`), for a subgroup `K'` of `H'`. `mem_awayLevel`,
  `awayHom_mem_awayLevel`, and `factorHom_mul_awayLevel`: `factorHom e h`
  commutes with every element of `awayLevel e K'`.
- `splitLevel e U K'`: the subgroup `e⁻¹ (U × K')` of `G`, for subgroups `U`
  of `H` and `K'` of `H'`. `mem_splitLevel` (`g ∈ splitLevel e U K'` iff
  `(e g).1 ∈ U` and `(e g).2 ∈ K'`), `factorHom_mem_splitLevel`,
  `awayLevel_le_splitLevel`.
- `awayLevelForms R e ι V K'` (abbreviation): `forms ι (awayLevel e K')` for
  the trivial representation on `V`, the functions `f : G → V` with
  `f (ι γ * g) = f g` and `f (g * k) = f g` for `k ∈ e⁻¹ (1 × K')`.
- `factorTranslation R e ι V K'`: the representation of `H` on
  `awayLevelForms R e ι V K'` by `(h • f) g = f (g * e⁻¹ (h, 1))`, the
  published `rightTranslation` along `factorHom e`
  (`factorTranslation_apply_coe`).
- `awayTranslate R e ι V g hg`, for `g : H'` with `g⁻¹ * k * g ∈ L` for all
  `k ∈ K`: the `R`-linear map `f ↦ (x ↦ f (x * e⁻¹ (1, g)))` from
  `awayLevelForms` at `L` to `awayLevelForms` at `K`
  (`awayTranslate_apply_coe`).
- `awayTranslateIntertwining R e ι V g hg`: `awayTranslate` as an intertwining
  map from `factorTranslation` at `L` to `factorTranslation` at `K`; the two
  factors commute (`factorHom_commute_awayHom`).
- `factorFormsPresheaf R e ι V : (CompactOpenLevel H')ᵒᵖ ⥤ Rep R H`: at `K'`
  the representation `factorTranslation` at `K'.subgroup`; on an arrow `a`
  the map `awayTranslateIntertwining` for `a.element`.
- `factorFixedEquiv R e ι V K' U`: for a subgroup `U` of `H`, the vectors of
  `factorTranslation` at `K'` fixed by `U` are `R`-linearly equivalent to
  `forms ι (splitLevel e U K')` for the trivial representation, by the
  identity on functions (`factorFixedEquiv_apply_coe`). Every
  `k ∈ e⁻¹ (U × K')` is `e⁻¹ ((e k).1, 1) * e⁻¹ (1, (e k).2)`.
- `isSmoothVector_factorTranslation_iff`: a form of level `e⁻¹ (1 × K')` is a
  smooth vector for `factorTranslation` if and only if it is a form of level
  `e⁻¹ (U × K')` for some open subgroup `U` of `H`.
- `splitLevel_eq_transport`: for compact open levels `U` of `H` and `K'` of
  `H'`, `splitLevel e U K'` is the subgroup of the published compact open level
  `CompactOpenLevel.transport e.symm (CompactOpenLevel.prod U K')` of `G`.

With `[IsTopologicalGroup H]`:

- `factorSmoothPresheaf R e ι V : (CompactOpenLevel H')ᵒᵖ ⥤ SmoothRep R H`:
  `factorFormsPresheaf` followed by `SmoothRep.smoothPartFunctor`.
- `factorSmoothFixedEquiv R e ι V K' U`: for an open subgroup `U` of `H`, the
  vectors of the smooth part of `factorTranslation` at `K'` fixed by `U` are
  the forms of level `e⁻¹ (U × K')` (`smoothPartFixedVectorsEquiv` followed by
  `factorFixedEquiv`; `factorSmoothFixedEquiv_apply_coe`).

## `Ext`, the hyperext spectral sequence and its abutment, level by level

Namespace `Langlands.Shimura.EquivariantForms`, section `Ext`. Here `R`, `G`,
`H` and `V` lie in one universe `u`, as the published smooth `Ext` requires,
and `H` is a topological group. Below `A(K')` denotes the smooth
representation `(factorSmoothPresheaf R e ι V).obj (op K')`. The letter `n`
in these declarations is a total degree, not Harris's rank `n`.

- `factorExtPresheaf R e ι V W i`: for a smooth representation `W` of `H` and
  `i : ℕ`, the presheaf of `R`-modules `K' ↦ Ext^i(W, A(K'))`, that is
  `factorSmoothPresheaf ⋙ SmoothExt.ext R H W i`.

With `[HasDerivedCategory.{w} (SmoothRep R H)]` and an object `X` of the
derived category of `SmoothRep R H`:

- `factorSpectralSequence R e ι V X K'`: the published
  `hyperextSpectralSequence` for the canonical t-structure, of `X` and of
  `A(K')` placed in degree `0` (`(singleFunctor _ 0).obj`).
- `factorSecondPageAddEquiv R e ι V X K' p q`: the object in position
  `(p, q)` of page 2 of `factorSpectralSequence X K'` is additively equivalent
  to `(factorExtPresheaf R e ι V (H^{-q}(X)) p).obj (op K')`, that is
  `Ext^p(H^{-q}(X), A(K'))`; this is the published `secondPageAddEquiv`.
- `factorAbutmentPresheaf R e ι V X n`: the presheaf of abelian groups
  `K' ↦ Hom(X, A(K')[n])` (`factorSmoothPresheaf` followed by
  `singleFunctor _ 0`, the shift by `n` and `preadditiveCoyoneda.obj (op X)`),
  the intended abutment in total degree `n`.
- `factorAbutmentIso R e ι V X K' n`: the term in degree `n` of the published
  `hyperextSpectralObject` of `X` and `A(K')` at the arrow `⊥ ⟶ ⊤` of `EInt`
  is isomorphic to the value at `K'` of `factorAbutmentPresheaf X n` (the
  published `abutmentIso`). This identifies a term of the spectral object; it
  is not a convergence statement, and convergence is not proved.
- `factorFiltrationPresheaf R e ι V X n p` and
  `factorGradedPresheaf R e ι V X n p`: the step `F^p` of the published
  abutment filtration of `Hom(X, A(K')[n])`, and its graded piece
  `gr^p = F^p / F^{p+1}`, as presheaves of abelian groups in `K'`. On arrows
  they are postcomposition with `A(a)` placed in degree `0`
  (`filtrationPostcomp`, `gradedPostcomp`); functoriality is the published
  `_id` and `_comp` lemmas.

## Harris's case

Namespace `Langlands.Shimura.DefiniteForms`. `A` is a finite-dimensional
`ℚ`-algebra with involution `σ : AlgebraInvolution ℚ A`, `p : ℕ` with
`hp : p ≠ 0`, and `R`, `V` and `A` lie in one universe `u`. `σ.DividingPoints p`
is `GJ(∏_{v ∣ p} ℚ_v)`, `σ.PrimeToPoints p` is `GJ(𝔸_f^{(p)})`, and the
published `σ.finiteAdelicPointsSplit p hp` is the splitting
`GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`. All declarations below are
the generic ones for `e = σ.finiteAdelicPointsSplit p hp` and
`ι = σ.finiteAdelicDiagonal`.

- `dividingSmoothPresheaf σ p hp R V`: the presheaf of smooth representations
  of `GJ(∏_{v ∣ p} ℚ_v)` on compact open levels `K'` of `GJ(𝔸_f^{(p)})`, at
  `K'` the smooth part of right translation on the functions
  `GJ(ℚ) \ GJ(𝔸_f) / (1 × K') → V`.
- `dividingSmoothFixedEquiv σ p hp R V K' U`: its vectors at `K'` fixed by an
  open subgroup `U` of `GJ(∏_{v ∣ p} ℚ_v)` are the forms of level `U × K'`.
- `dividingExtPresheaf σ p hp R V W i`: `K' ↦ Ext^i(W, A(K'))` for a smooth
  representation `W` of `GJ(∏_{v ∣ p} ℚ_v)`.
- With `[HasDerivedCategory.{w} (SmoothRep R (σ.DividingPoints p))]`:
  `dividingSpectralSequence σ p hp R V X K'`,
  `dividingSecondPageAddEquiv σ p hp R V X K' i j` (page 2 in position
  `(i, j)` is `Ext^i(H^{-j}(X), A(K'))`), `dividingAbutmentPresheaf`,
  `dividingAbutmentIso`, `dividingFiltrationPresheaf` and
  `dividingGradedPresheaf`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4. Worker 61 read the rendered scanned page,
printed p.309 (one-based PDF page 11). It writes `K(m)^p = K'^{,p} × K_ℓ(m)`
and gives the isomorphism (4.3)
"`[(GJ(ℚ)\GJ(𝔸_f)/K(m)^p) × M̌_N]/GJ_p ⥲ S(GG, X_{n-1})_{K(N,m)} ×_{𝒦,v_1} F^nr`".
It continues: "Let `𝓛` be a free `𝒪/ℓ^m𝒪`-module, and let `𝓛~` denote the
corresponding constant étale sheaf on `S(GG, X_{n-1})_{K(N,m)}`. Write
`𝒪_m = 𝒪/ℓ^m𝒪`." Proposition 4.4: "There is a spectral sequence of
`𝒪_m`-modules (4.4.1)
`E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, 𝒪_m(n-1)), 𝒜_ℓ(GJ, 𝓛, K(m))) ⇒
H^{i+j}(S̄_{K(N,m)}, 𝓛~)`. Here `Ext^i` denotes the `i`-th derived functor of
`Hom` in the category of smooth `𝒪_m[GJ]`-modules. Moreover, as
`K(N,m)^p`-varies the spectral sequences are `GG(𝔸_f^p)`-equivariant."

How the module relates to Harris (an explanation, not formalized):

- The second argument. In (4.4.1) `GJ` acts through `GJ_p`, so we read
  `𝒜_ℓ(GJ, 𝓛, K(m))` as the functions on `GJ(ℚ)\GJ(𝔸_f)/K(m)^p` with values
  in `𝓛`, the space appearing in (4.3). `GJ_p` acts by right translation. With
  the constant sheaf `𝓛~` the coefficients carry the trivial action. We take
  the smooth part of this action, since `Ext` is computed among smooth
  modules. The away level `K(m)^p` is an arbitrary compact open level `K'` of
  `GJ(𝔸_f^{(p)})`. For `p` prime, `∏_{v ∣ p} ℚ_v` is `ℚ_p` and
  `σ.DividingPoints p` is `GJ_p`.
- `dividingSmoothFixedEquiv` supports this reading: the vectors fixed by an
  open subgroup `U` of `GJ_p` are the forms of level `U × K'`, Harris's
  `𝒜_ℓ(GJ, 𝓛, K)` with trivial coefficients at a level `K` with
  `p`-component `U`.
- Coefficients. Harris's `𝓛` is a free `𝒪_m`-module. Here `V` is any module
  over any commutative ring `R`, and `Ext` is taken in smooth
  `R`-representations. Harris's case is `R = 𝒪_m` and `V = 𝓛`.
- The first argument. We do not construct `M̌_N` or its compactly supported
  cohomology. The spectral sequence takes any object `X` of the derived
  category of smooth representations; its page 2 in position `(i, j)` is
  `Ext^i(H^{-j}(X), A(K'))`. Harris's term arises when
  `H^{-j}(X) = H_c^{2(n-1)-j}(M̌_N, 𝒪_m(n-1))`, for instance for a complex
  computing that cohomology shifted by `2(n-1)`. This is an interpretation
  and is not formalized.
- The abutment. The spectral sequence is the published hyperext spectral
  sequence; its intended abutment is `Hom(X, A(K')[n])`. Neither its
  convergence nor any comparison with `H^{i+j}(S̄_{K(N,m)}, 𝓛~)` is proved.
- Equivariance. We model "as `K(N,m)^p` varies" by presheaves on the category
  of compact open levels `K'` of `GJ(𝔸_f^{(p)})`. Its arrows include
  inclusions of levels and right translations by elements of
  `GJ(𝔸_f^{(p)})`. The page-2 terms (`dividingExtPresheaf`), the abutment and
  its filtration steps and graded pieces are such presheaves. The
  identification of `GG(𝔸_f^p)` with `GJ(𝔸_f^p)` that Harris uses is not
  formalized; we work with `GJ(𝔸_f^{(p)})` directly.
- All declarations are ours, derived from Mathlib and the published modules
  named above. `awayLevel`, `splitLevel`, `awayTranslate`, `factorFixedEquiv`
  and the generic `factor*` presheaves are internal constructions not printed
  in Harris 1999.

## Related declarations

- Library `Langlands.Shimura.EquivariantForms.smoothFormsFunctor`
  (`Shimura/EquivariantForms`): smooth parts of `rightTranslation`, functorial
  in the coefficient representation at one fixed level. At `K'`,
  `factorSmoothPresheaf` is its value on the trivial representation of
  `awayLevel e K'`. The new presheaf varies the level instead.
- Library `Langlands.Shimura.DefiniteForms.ellModuleForms`
  (`Shimura/DefiniteFormsDoubleCoset`): Harris's `𝒜_ℓ(GJ, 𝓛, K)` for a
  representation of `K_ℓ`. With trivial coefficients it is the `forms` space on
  the right of `dividingSmoothFixedEquiv` at `K = splitLevel e U K'`.
- Library `Langlands.Shimura.LevelColimit.awaySmoothRep`
  (`Shimura/SplitLevelTower`, Worker 13): the smooth representation of the
  second factor `H'` on the colimit, over the away levels at a fixed level `K₀`
  of `H`, of a presheaf on levels of `G`. That is the geometric side with the
  roles of the factors exchanged. The present module keeps the away level
  `K'` and lets the first factor act.
- Library `Langlands.Cohomology.SmoothHyperext.secondPageAddEquiv`
  (`Cohomology/SmoothHyperextSecondPage`): the generic identification of
  page 2 used by `factorSecondPageAddEquiv`.

## Scope

The module provides the smooth `GJ_p`-modules of forms with trivial
coefficients, their `Ext` groups, the hyperext spectral sequence of any
complex `X` against them, and the level-by-level presheaves of page-2 terms,
abutments, filtrations and graded pieces. It does not:

- construct `M̌_N` or the Shimura varieties, or prove (4.3);
- prove convergence or the comparison with the cohomology of `S̄_{K(N,m)}`;
- assemble the spectral sequences into a presheaf of spectral sequences
  (maps of spectral sequences between levels, compatible with differentials);
- prove that `factorSecondPageAddEquiv` is natural in `K'`;
- treat coefficients with a nontrivial `K_ℓ` action, or Hecke operators beyond
  the arrows of the level category.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
