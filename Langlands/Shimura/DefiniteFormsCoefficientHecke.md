# Hecke operators on forms with `K_ℓ`-coefficients and on their `Ext` groups (Proposition 4.10)

Author: Worker 61. Built on Worker 61's published
`Langlands.Shimura.DefiniteFormsSmoothCoefficients` (`coefficientDomain`,
`awayHom_mem_of_mem_coefficientDomain`, `awayLevel_domainLevel_le`,
`coefficientForms`, `coefficientTranslation`, `coefficientTransport`,
`coefficientFormsPresheaf`, `coefficientSmoothPresheaf`,
`coefficientExtPresheaf`, `coefficientAbutmentPresheaf`,
`coefficientFiltrationPresheaf`, `coefficientGradedPresheaf`,
`localCoefficientRep`, `dividingCoefficientDomain` and the
`dividingCoefficient*Presheaf` specializations),
`Langlands.Shimura.DefiniteFormsHeckeExt` (`endRingHom`, the additivity of
`SmoothExt.ext R H W i`, `filtrationFunctor_additive`,
`gradedFunctor_additive`), `Langlands.Shimura.DefiniteFormsSmoothExt`
(`mem_awayLevel`, `awayHom_mem_awayLevel`),
`Langlands.Cohomology.HyperextAbutmentFunctor`
(`HyperextAbutment.filtrationFunctor`, `gradedFunctor`, `filtrationι`,
`gradedπ`) and `Langlands.Cohomology.HyperextAbutmentNaturality`
(`filtrationPostcomp`, `gradedPostcomp`). It is also built on the published
`Langlands.Shimura.LevelHecke` (`heckeOperator`, `HeckeCosets`,
`heckeOperator_apply_out`, `heckeOperator_one_of_le`,
`fixedVectorsMap_heckeOperator`), `Langlands.Shimura.LevelHeckeAlgebra`
(`LevelHeckeAlgebra`, its module structure on fixed vectors, `heckeAct`,
`fixedVectorsMap_heckeAct`, `doubleCoset`, `doubleCoset_smul`),
`Langlands.Shimura.LevelHeckeCompose` (`heckeOperator_eq_comp_translateFixed`,
`translateFixed_apply_coe`) and `Langlands.Shimura.LevelColimit`
(`mem_conjLevel`); on Worker 13's published
`Langlands.Shimura.SplitLevelTower` (`factorHom`, `awayHom`,
`factorHom_commute_awayHom`), `Langlands.Shimura.Unitary.PointsSplit`
(`DividingPoints`, `PrimeToPoints`, `finiteAdelicPointsSplit`) and
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`); on the published
`Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`); and on Worker 57's published
`Langlands.Shimura.Levels` (`CompactOpenLevel` and its arrows) and
`Langlands.Shimura.Unitary.Adelic` (`finiteAdelicDiagonal`). From Mathlib it
uses representations and `Rep`, endomorphism rings in preadditive categories,
derived categories with their canonical t-structure
(`DerivedCategory.TStructure.t`, `singleFunctor`, shifts) and
`preadditiveCoyoneda`.

The published `DefiniteFormsSmoothCoefficients` models Harris's "as
`K(N)^{ℓ,p}`-varies the spectral sequences are `GG(𝔸_f^{ℓ,p})`-equivariant"
in Proposition 4.10 by presheaves on the category of compact open levels of
the coefficient domain. The published `DefiniteFormsHeckeExt` adds the Hecke
operators at a fixed level for Proposition 4.4, whose coefficients carry the
trivial action. This module does the same for Proposition 4.10, whose
coefficients are a representation `ρ`. For compact open levels `K`, `L` of the
coefficient domain and an element `g` of it, it defines the double-coset
operator `[K g L]` from the value at `L` to the value at `K` of each of the
published presheaves: the forms with coefficients `ρ`, their smooth parts,
`Ext^i(W, -)`, and the abutment with its filtration steps and graded pieces.
It also defines the action of the Hecke algebra of `K` on the value at `K`,
as a ring homomorphism. It shows that the map of each presheaf along an arrow
of levels is the double-coset operator of the arrow's element. The operators
and the Hecke algebra are the published ones of `LevelHecke` and
`LevelHeckeAlgebra`, applied to a representation of the coefficient domain on
the forms of trivial level. In that representation an element acts by right
translation and also on the coefficients. Everything is done for a group `G`
with a splitting `e : G ≃ₜ* H × H'`, a subgroup `D` of `G` and a
representation `ρ` of `D`. It is then specialized to Harris's
`GJ(𝔸_f) ≃ GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`, with `D` the finite adelic
points whose `ℓ`-component lies in `K_ℓ`.

## Conventions

`R` is a commutative ring and `V` an `R`-module. `Γ`, `G`, `H`, `H'` are
groups, `ι : Γ →* G`, and `G`, `H`, `H'` carry topologies.
`e : G ≃ₜ* H × H'` is an isomorphism of topological groups. The published
`factorHom e h = e⁻¹ (h, 1)` and `awayHom e h' = e⁻¹ (1, h')` embed the two
factors in `G`; they commute elementwise.

`D` is a subgroup of `G` and `ρ` a representation of `D` on `V`. The published
`coefficientDomain e D` is the subgroup of `H'` of the `c` with
`e⁻¹ (1, c) ∈ D`. For a subgroup `K'` of it, the published
`coefficientForms R e ι ρ K'` consists of the functions `f : G → V` with
`f (ι γ * x) = f x` and `f (x * k) = ρ k⁻¹ (f x)` for `k ∈ e⁻¹ (1 × K')`. The
published `coefficientTranslation R e ι ρ K'` is right translation
`(h • f) x = f (x * e⁻¹ (h, 1))` by `H` on them. The published
`coefficientTransport R e ι ρ c hc`, for `c` in the coefficient domain with
`c⁻¹ * k * c ∈ K₂` for `k ∈ K₁`, maps the forms at `K₂` to the forms at `K₁` by
`f ↦ (x ↦ ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c))))`.

`CompactOpenLevel C` is the published category of compact open subgroups of a
topological group `C`; below `C` is the coefficient domain with the subspace
topology of `H'`. An arrow `a : K ⟶ L` is an element `a.element = c` of `C`
with `c⁻¹ * k * c ∈ L` for all `k ∈ K` (`a.respects`). The published
presheaves `coefficientFormsPresheaf`, `coefficientSmoothPresheaf`,
`coefficientExtPresheaf W i`, `coefficientAbutmentPresheaf X n`,
`coefficientFiltrationPresheaf X n p` and `coefficientGradedPresheaf X n p`
are functors out of `(CompactOpenLevel C)ᵒᵖ`. At `K` their values are the
forms of level `e⁻¹ (1 × K)` with coefficients `ρ` as a representation of
`H`, their smooth part `A(K)`, `Ext^i(W, A(K))`, `Hom(X, A(K)[n])`, and the
step `F^p` and graded piece `gr^p` of the abutment filtration on it. On an
arrow `a` their map is induced by `coefficientTransport` along `a.element`.

For a representation `π` of a topological group `C` and compact open levels
`K`, `L`, the published `LevelHecke.heckeOperator π K L g : V^L →ₗ V^K` is
`[K g L] v = ∑ π (k g) v` over representatives `k` of `K / (K ∩ g L g⁻¹)`
(`HeckeCosets K L g`). The published `LevelHeckeAlgebra R K` is the Hecke
algebra of `K`: the `K`-fixed vectors of `R[C/K]`, with convolution. It acts on
`V^K` by `LevelHecke.heckeAct`, `a • v = ∑_{xK} a(xK) π(x) v`. The element
`doubleCoset K g` acts by `[K g K]` (`doubleCoset_smul`).

For an object `Y` of a preadditive category, `End Y` is Mathlib's
endomorphism ring, with multiplication `f * f' = f' ≫ f`. The published
`endRingHom F Y : End Y →+* End (F.obj Y)` is `F.map` for an additive functor
`F`.

## Generic declarations

Namespace `Langlands.Shimura.EquivariantForms`.

Section `CoefficientTranslation` (universes arbitrary):

- `conj_mem_bot e c`: every element `c` of the coefficient domain conjugates
  the trivial subgroup into itself, so `coefficientTransport` along `c` maps
  the forms of trivial level to themselves.
- `coefficientAwayTranslation R e ι ρ`: the representation of the coefficient
  domain on the forms of trivial level `coefficientForms R e ι ρ ⊥` (all
  left `ι Γ`-invariant functions `G → V`) by
  `(c • f) x = ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c)))`, which is
  `coefficientTransport` along `c` (`coefficientAwayTranslation_apply_coe`).
  It is multiplicative because `ρ` and `awayHom e` are homomorphisms.
- `coefficientTranslationIntertwining R e ι ρ h`: right translation by
  `h ∈ H` on the forms of trivial level, as an intertwining map of
  `coefficientAwayTranslation`, since the two factors commute.
- `coefficientAwayFixedEquiv R e ι ρ K'`: the vectors of
  `coefficientAwayTranslation` fixed by a subgroup `K'` of the coefficient
  domain are `R`-linearly equivalent to `coefficientForms R e ι ρ K'`, by the
  identity on functions (`coefficientAwayFixedEquiv_apply_coe`,
  `coefficientAwayFixedEquiv_symm_apply_coe`). Indeed `c • f = f` says
  `f (x * e⁻¹ (1, c)) = ρ (e⁻¹ (1, c))⁻¹ (f x)`, the defining condition of
  `coefficientForms` at `K'`.

Section `CoefficientHecke` (universes arbitrary; `H'` a topological group).
Here `K`, `L` are compact open levels of the coefficient domain and `g` is in
it.

- `coefficientHecke R e ι ρ K L g`: the `R`-linear operator `[K g L]` from
  `coefficientForms R e ι ρ L` to `coefficientForms R e ι ρ K`. It is the
  published `heckeOperator (coefficientAwayTranslation R e ι ρ) K L g`
  transported by `coefficientAwayFixedEquiv`. `coefficientHecke_apply_coe`:
  `([K g L] f) x = ∑ ρ (e⁻¹ (1, k g)) (f (x * e⁻¹ (1, k g)))` over
  `q : HeckeCosets K L g`, with `k = q.out`.
- `coefficientHeckeIntertwining R e ι ρ K L g`: `coefficientHecke` as an
  intertwining map between the `coefficientTranslation` representations at
  `L` and at `K`; its proof is the published `fixedVectorsMap_heckeOperator`
  applied to `coefficientTranslationIntertwining`.
- `coefficientHeckeHom R e ι ρ K L g`: the same as a morphism of `Rep R H`
  from `(coefficientFormsPresheaf R e ι ρ).obj (op L)` to the value at `K`.
- `coefficientHecke_eq_coefficientTransport`: if `g⁻¹ * k * g ∈ L` for all
  `k ∈ K`, then `[K g L]` is `coefficientTransport` along `g`. The proof
  writes `[K g L]` as the inclusion `[K 1 g L g⁻¹]` after translation by `g`
  (`heckeOperator_eq_comp_translateFixed`, `heckeOperator_one_of_le`).
- `coefficientFormsPresheaf_map_eq`: for an arrow `a : K ⟶ L`, the map
  `(coefficientFormsPresheaf R e ι ρ).map a.op` is
  `coefficientHeckeHom R e ι ρ K L a.element`.
- `coefficientHeckeHom_self`: `[K 1 K]` is the identity.
- `coefficientHeckeAct R e ι ρ K a`,
  `coefficientHeckeActIntertwining R e ι ρ K a`: the action of
  `a : LevelHeckeAlgebra R K.subgroup` on `coefficientForms R e ι ρ K`, the
  published `heckeAct` of `coefficientAwayTranslation` transported by
  `coefficientAwayFixedEquiv`, and the fact that it commutes with
  `coefficientTranslation` (published `fixedVectorsMap_heckeAct`).
- `coefficientFormsHeckeAlgebraHom R e ι ρ K :
  LevelHeckeAlgebra R K.subgroup →+* End ((coefficientFormsPresheaf R e ι ρ).obj (op K))`,
  `a ↦ coefficientHeckeActIntertwining R e ι ρ K a`. It is a ring
  homomorphism because the action of the Hecke algebra on fixed vectors is a
  module structure (`one_smul`, `mul_smul`, `zero_smul`, `add_smul`).
- `coefficientFormsHeckeAlgebraHom_doubleCoset`: `doubleCoset K g` maps to
  `coefficientHeckeHom R e ι ρ K K g`.

Section `CoefficientHeckeSmooth` (universes arbitrary; `H`, `H'` topological
groups):

- `coefficientSmoothHeckeHom R e ι ρ K L g`: `SmoothRep.smoothPartFunctor`
  applied to `coefficientHeckeHom`, a morphism of smooth representations of
  `H` between the values of `coefficientSmoothPresheaf` at `L` and at `K`.
- `coefficientSmoothPresheaf_map_eq`: the map of `coefficientSmoothPresheaf`
  along `a : K ⟶ L` is `coefficientSmoothHeckeHom R e ι ρ K L a.element`.
- `coefficientSmoothHeckeAlgebraHom R e ι ρ K`: `coefficientFormsHeckeAlgebraHom`
  followed by `endRingHom` of the smooth-part functor, a ring homomorphism
  from the Hecke algebra of `K` to
  `End ((coefficientSmoothPresheaf R e ι ρ).obj (op K))`;
  `coefficientSmoothHeckeAlgebraHom_doubleCoset`.

Section `CoefficientHeckeExt`: `R`, `G`, `H` and `V` lie in one universe `u`,
as the published smooth `Ext` requires. `W` is a smooth representation of `H`
and `i : ℕ`.

- `coefficientExtHecke R e ι ρ W i K L g`: `Ext^i(W, -)` (the published
  `SmoothExt.ext R H W i`) applied to `coefficientSmoothHeckeHom`, an
  `R`-linear map from `Ext^i(W, A(L))` to `Ext^i(W, A(K))`.
- `coefficientExtPresheaf_map_eq`: the map of
  `coefficientExtPresheaf R e ι ρ W i` along `a : K ⟶ L` is
  `coefficientExtHecke R e ι ρ W i K L a.element`.
- `coefficientExtHeckeAlgebraHom R e ι ρ W i K`: the Hecke algebra of `K`
  acting on `Ext^i(W, A(K))`, a ring homomorphism to its endomorphisms in
  `ModuleCat R` (through `endRingHom` and the published additivity of
  `SmoothExt.ext R H W i`); `coefficientExtHeckeAlgebraHom_doubleCoset`.

Section `CoefficientHeckeAbutment`, with
`[HasDerivedCategory.{w} (SmoothRep R H)]` and an object `X` of the derived
category of `SmoothRep R H`. The letter `n` is a total degree and `p` a
filtration index.

- `coefficientAbutmentHecke R e ι ρ X n K L g`: postcomposition with
  `coefficientSmoothHeckeHom` (placed in degree `0` and shifted by `n`), from
  `Hom(X, A(L)[n])` to `Hom(X, A(K)[n])`;
  `coefficientAbutmentPresheaf_map_eq`;
  `coefficientAbutmentHeckeAlgebraHom R e ι ρ X n K` with
  `coefficientAbutmentHeckeAlgebraHom_doubleCoset`.
- `coefficientFiltrationHecke R e ι ρ X n p K L g`: the published
  `filtrationFunctor` applied to `coefficientSmoothHeckeHom` placed in
  degree `0`, from `F^p` at `L` to `F^p` at `K`;
  `coefficientFiltrationPresheaf_map_eq`;
  `coefficientFiltrationHecke_comp_filtrationι` (it commutes with the
  inclusions `F^p ⊆ Hom(X, A(-)[n])`);
  `coefficientFiltrationHeckeAlgebraHom R e ι ρ X n p K` with
  `coefficientFiltrationHeckeAlgebraHom_doubleCoset`.
- `coefficientGradedHecke R e ι ρ X n p K L g`: the same for `gr^p`;
  `coefficientGradedPresheaf_map_eq`;
  `coefficientFiltrationHecke_comp_gradedπ` (it commutes with the projections
  `F^p ⟶ gr^p`); `coefficientGradedHeckeAlgebraHom R e ι ρ X n p K` with
  `coefficientGradedHeckeAlgebraHom_doubleCoset`.

The ring homomorphisms to `End` of the abutment, filtration and graded
values are into endomorphisms in `AddCommGrpCat`.

## Harris's case

Namespace `Langlands.Shimura.DefiniteForms`. `A` is a finite-dimensional
`ℚ`-algebra with involution `σ : AlgebraInvolution ℚ A`, `ℓ : FinitePlace ℚ`
a finite place, `Kℓ` a subgroup of the `ℓ`-adic points
`σ.Points (FiniteCompletion ℚ ℓ)`, `𝓛` a representation of `Kℓ` on an
`R`-module `V`, and `p : ℕ` with `hp : p ≠ 0`; `A`, `R` and `V` lie in one
universe `u`. `σ.DividingPoints p` is `GJ(∏_{v ∣ p} ℚ_v)`,
`σ.PrimeToPoints p` is `GJ(𝔸_f^{(p)})`, and the declarations are the generic
ones for the published splitting `e = σ.finiteAdelicPointsSplit p hp`,
`ι = σ.finiteAdelicDiagonal` and `ρ = localCoefficientRep σ ℓ Kℓ 𝓛`, under
which `g ∈ GJ(𝔸_f)` with `g_ℓ ∈ Kℓ` acts on `V` by `𝓛 (g_ℓ)`. `K`, `L` are
compact open levels of the published `dividingCoefficientDomain σ ℓ Kℓ p hp`
(the `k ∈ GJ(𝔸_f^{(p)})` such that the `ℓ`-component of `e⁻¹ (1, k)` lies in
`Kℓ`) and `g` is in it.

- `dividingCoefficientSmoothHecke σ ℓ Kℓ 𝓛 p hp K L g`,
  `dividingCoefficientSmoothPresheaf_map_eq`,
  `dividingCoefficientSmoothHeckeAlgebraHom σ ℓ Kℓ 𝓛 p hp K`,
  `dividingCoefficientSmoothHeckeAlgebraHom_doubleCoset`: `[K g L]` and the
  Hecke algebra of `K` on the published `dividingCoefficientSmoothPresheaf`,
  as morphisms of smooth representations of `GJ(∏_{v ∣ p} ℚ_v)`.
- `dividingCoefficientExtHecke σ ℓ Kℓ 𝓛 p hp W i K L g`,
  `dividingCoefficientExtPresheaf_map_eq`,
  `dividingCoefficientExtHeckeAlgebraHom σ ℓ Kℓ 𝓛 p hp W i K`,
  `dividingCoefficientExtHeckeAlgebraHom_doubleCoset`: the same on
  `Ext^i(W, -)` for a smooth representation `W` of `GJ(∏_{v ∣ p} ℚ_v)`, the
  page-2 terms of the published `dividingCoefficientSpectralSequence` up to
  the published `dividingCoefficientSecondPageAddEquiv`.
- With `[HasDerivedCategory.{w} (SmoothRep R (σ.DividingPoints p))]`:
  `dividingCoefficientAbutmentHecke σ ℓ Kℓ 𝓛 p hp X n K L g`,
  `dividingCoefficientAbutmentPresheaf_map_eq`,
  `dividingCoefficientAbutmentHeckeAlgebraHom σ ℓ Kℓ 𝓛 p hp X n K`, and the
  same for the step `F^i` (`dividingCoefficientFiltrationHecke`,
  `dividingCoefficientFiltrationPresheaf_map_eq`,
  `dividingCoefficientFiltrationHeckeAlgebraHom`) and the graded piece `gr^i`
  (`dividingCoefficientGradedHecke`,
  `dividingCoefficientGradedPresheaf_map_eq`,
  `dividingCoefficientGradedHeckeAlgebraHom`) of the abutment filtration. The
  `doubleCoset` lemmas for these three are the generic ones.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4. Worker 61 read the rendered scanned
page, printed p.311 (one-based PDF page 13): "Proposition 4.10. There is a
spectral sequence of `𝒪`-modules (4.10.1)
`E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒
H^{i+j}(S̄_{K(N)}, W̃)`. Here `Ext^i` denotes the `i`-th derived functor of
`Hom` in the category of smooth `L_ℓ[GJ]`-modules. Moreover, as
`K(N)^{ℓ,p}`-varies the spectral sequences are
`GG(𝔸_f^{ℓ,p})`-equivariant." On the same page, about the finite-level
spectral sequence (4.4.1) with coefficients `𝓛_m`: it "is still
`K_{ℓ,m}`-equivariant—though the action is no longer trivial". Harris's (3.7)
for a representation of `K_ℓ`, `f(gk) = ρ(k_ℓ)^{-1} f(g)`, is quoted in the
published `DefiniteFormsDoubleCoset.md` (printed p.308).

How the module relates to Harris (an explanation, not formalized):

- Equivariance at a fixed level. The published
  `DefiniteFormsSmoothCoefficients` reads "as `K(N)^{ℓ,p}` varies" as a
  presheaf on compact open levels of the coefficient domain, whose arrows are
  inclusions of levels and transports by elements `g` with `g⁻¹ K g ⊆ L`.
  For the forms, the coefficient domain acts on the forms of trivial level by
  `(c • f) x = ρ(c_ℓ) f(x c)` (`coefficientAwayTranslation`), and its
  `K`-fixed vectors are exactly the forms of level `K` satisfying (3.7)
  (`coefficientAwayFixedEquiv`). On these invariants, the equivariance is the
  action of the double-coset operators `[K g L]` for all `g`, and of the
  Hecke algebra of `K`. This module defines these operators on each term of
  the published presheaves. On the terms `Ext^i(W, A(K))`, the abutment and
  its filtration, they are defined by functoriality of the term in `A(K)`, not
  from an action on a limit or colimit over the levels.
- Compatibility with the presheaves. `coefficientFormsPresheaf_map_eq` and its
  analogues show that the maps of the presheaves along arrows are the
  operators `[K g L]` of the arrow's element. So the operators extend the
  equivariance of `DefiniteFormsSmoothCoefficients` from the arrows to all
  double cosets.
- The group. The elements `g` range over the coefficient domain, the
  `g ∈ GJ(𝔸_f^{(p)})` whose `e⁻¹ (1, g)` has `ℓ`-component in `Kℓ`. For
  `ℓ ∤ p` this contains the elements of `GJ(𝔸_f^{ℓ,p})` (trivial
  `ℓ`-component), which act by plain right translation, and also elements
  with nontrivial `ℓ`-component, which also act on the coefficients (compare
  Harris's "the action is no longer trivial"). These facts and the
  identification of `GG(𝔸_f^{ℓ,p})` with `GJ(𝔸_f^{ℓ,p})` that Harris uses are
  not formalized. In `[K g L]` the representatives `k` of `K / (K ∩ g L g⁻¹)`
  may have nontrivial `ℓ`-component, so the factor `ρ (e⁻¹ (1, k g))` in
  `coefficientHecke_apply_coe` is not the identity in general even for `g`
  with trivial `ℓ`-component.
- Which Hecke algebra. The operators and the Hecke algebra are the published
  `LevelHecke.heckeOperator`, `LevelHeckeAlgebra` and `heckeAct`, for the
  representation `coefficientAwayTranslation`. Since all values are taken
  through these published constructions, the Hecke algebras here are the same
  objects as the ones in the published level-Hecke modules and in
  `DefiniteFormsHeckeExt`, for the group `coefficientDomain e D` in place of
  `H'`.
- Hecke operators on the spectral sequence. Harris's statement asserts
  equivariance of the spectral sequences, including their differentials. This
  module provides the operators on the page-2 terms
  (`dividingCoefficientExtHecke`, through the published
  `dividingCoefficientSecondPageAddEquiv`) and on the abutment, its filtration
  steps and graded pieces, and their compatibility with the inclusions
  `F^p ⊆ Hom(X, A(K)[n])` and projections `F^p ⟶ gr^p`. It does not show that
  the differentials of the spectral sequence, or the identification of
  page 2, commute with them.
- Coefficients and the limit over `m`. As in
  `DefiniteFormsSmoothCoefficients`, `𝓛` is any representation of any
  subgroup `Kℓ` on any `R`-module, and Harris's (4.10.1) is the case
  `R = L_ℓ`, `V = W(L_ℓ)`. The inverse systems over `m` of Worker 61's
  accepted `DefiniteFormsCoefficientSystem` (candidate
  `c927cd83-db7c-4c13-8b23-68b0ef825299`, not imported here) are not given
  Hecke operators in this module.
- All declarations are ours, derived from Mathlib and the published modules
  named above. `coefficientAwayTranslation`, `coefficientAwayFixedEquiv`,
  `coefficientHecke` and the `*Hecke*` maps and ring homomorphisms are
  internal constructions not printed in Harris 1999.

## Related declarations

- Library `Langlands.Shimura.EquivariantForms.heckeOperator`
  (`Shimura/EquivariantFormsHecke`): the operator `[K g L]` on forms for a
  representation `ρ` of all of `G` and compact open levels of `G`, with the
  same formula `∑ ρ (k g) (f (x k g))`. Here `ρ` is defined only on `D` and the
  levels and `g` lie in the second factor; a comparison of the two operators
  is not formalized.
- Library `Langlands.Shimura.EquivariantForms.awayHecke` and
  `formsHeckeAlgebraHom` (`Shimura/DefiniteFormsHeckeExt`): the case of
  trivial coefficients on all compact open levels of `H'`, which this module
  follows step by step. A comparison for `ρ` trivial is not formalized.
- Library `Langlands.Shimura.LevelHecke.heckeActionNatTrans`
  (`Shimura/LevelHeckeAction`): the double-coset operators as a natural
  transformation of fixed-vector functors on smooth representations. As in
  `DefiniteFormsHeckeExt`, the representation here is on forms of trivial
  level, which are not assumed smooth for the coefficient domain, so the
  operators are taken directly from `heckeOperator` and `heckeAct`.

## Scope

The module provides the double-coset operators `[K g L]` and the Hecke
algebra of `K` acting on the forms with coefficients in a representation of
`D` (in Harris's case, of `K_ℓ` through `g ↦ g_ℓ`), their smooth parts, their
`Ext` groups, and the intended abutment of the hyperext spectral sequence with
its filtration steps and graded pieces. It shows that the maps of the
published presheaves along arrows of levels are these operators. It does not:

- prove that the operators commute with the differentials of the spectral
  sequence or with `coefficientSecondPageAddEquiv`;
- prove composition laws for the operators `[K g L]` between different
  levels beyond those implied by the ring homomorphisms at one level;
- treat the inverse systems over `m`, the passage to `L_ℓ`-coefficients, or
  any Galois action;
- construct `M̌_N`, the Shimura varieties or their cohomology, or prove
  convergence or the comparison with `H^{i+j}(S̄_{K(N)}, W̃)`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
