# Hecke operators on forms with trivial coefficients and on their `Ext` groups (Proposition 4.4)

Author: Worker 61. Built on two modules of Worker 61 that have been
independently accepted but are not yet in the Library (commit 568f1cff):
`Langlands.Shimura.DefiniteFormsSmoothExt` (candidate
`687f402a-30ce-4e91-8e37-a5c30bf357a6`: `awayLevelForms`, `mem_awayLevel`,
`awayHom_mem_awayLevel`, `factorTranslation`, `awayTranslate`,
`factorFormsPresheaf`, `factorSmoothPresheaf`, `factorExtPresheaf`,
`factorAbutmentPresheaf`, `factorFiltrationPresheaf`, `factorGradedPresheaf`
and their `DefiniteForms.dividing*` specializations) and
`Langlands.Cohomology.HyperextAbutmentFunctor` (candidate
`8e1ba75f-07ac-4edf-8a61-c381b99cc033`:
`HyperextAbutment.filtrationFunctor`, `gradedFunctor`, `filtrationι`,
`gradedπ`). Both are included unchanged in this candidate's workspace and
must be integrated first. It is also built on the published
`Langlands.Shimura.LevelHecke` (`heckeOperator`, `HeckeCosets`,
`heckeOperator_apply_out`, `heckeOperator_one_of_le`,
`fixedVectorsMap_heckeOperator`), `Langlands.Shimura.LevelHeckeAlgebra`
(`LevelHeckeAlgebra`, its module structure on fixed vectors, `heckeAct`,
`fixedVectorsMap_heckeAct`, `doubleCoset`, `doubleCoset_smul`) and
`Langlands.Shimura.LevelHeckeCompose` (`heckeOperator_eq_comp_translateFixed`,
`translateFixed_apply_coe`); on Worker 61's published
`Langlands.Shimura.EquivariantForms` (`rightTranslation`),
`Langlands.Cohomology.HyperextAbutmentNaturality`
(`HyperextAbutment.filtrationPostcomp`, `gradedPostcomp`) and
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (additivity of
`SmoothRep.smoothPartFunctor`); on Worker 13's published
`Langlands.Shimura.SplitLevelTower` (`factorHom`, `awayHom`,
`factorHom_commute_awayHom`), `Langlands.Shimura.Unitary.PointsSplit`
(`DividingPoints`, `PrimeToPoints`, `finiteAdelicPointsSplit`),
`Langlands.Cohomology.SmoothHomComplex` (`SmoothHomComplex.homFunctor`) and
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`); on the published
`Langlands.Cohomology.RightDerivedAdditive` (additivity of right derived
functors) and `Langlands.Shimura.LevelColimit` (`mem_conjLevel`); and on
Worker 57's published `Langlands.Shimura.Levels` (`CompactOpenLevel` and its
arrows) and `Langlands.Shimura.Unitary.Adelic` (`finiteAdelicDiagonal`). From Mathlib it uses representations and `Rep`,
endomorphism rings in preadditive categories, additive functors, derived
categories with their canonical t-structure (`DerivedCategory.TStructure.t`,
`singleFunctor`, shifts) and `preadditiveCoyoneda`.

The accepted `DefiniteFormsSmoothExt` models Harris's "as `K(N,m)^p` varies
the spectral sequences are `GG(𝔸_f^p)`-equivariant" by presheaves on the
category of compact open levels away from `p`. This module adds the Hecke
operators at a fixed level. For compact open levels `K`, `L` away from `p` and
an element `g`, it defines the double-coset operator `[K g L]` from the value
at `L` to the value at `K` of each of those presheaves: the forms, their
smooth parts, `Ext^i(W, -)`, and the abutment with its filtration steps and
graded pieces. It also defines the action of the Hecke algebra of `K` on the
value at `K`, as a ring homomorphism. It shows that the map of each presheaf
along an arrow of levels is the double-coset operator of the arrow's element.
The operators and the Hecke algebra are the published ones of
`LevelHecke` and `LevelHeckeAlgebra`, which Worker 13's modules also use. Here
they are applied to the representation of the second factor by right
translation on the forms of trivial level. Everything is done for a group `G`
with a splitting `e : G ≃ₜ* H × H'` and then specialized to Harris's
`GJ(𝔸_f) ≃ GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`.

## Conventions

`R` is a commutative ring and `V` an `R`-module. `Γ`, `G`, `H`, `H'` are
groups, `ι : Γ →* G`, and `G`, `H`, `H'` carry topologies.
`e : G ≃ₜ* H × H'` is an isomorphism of topological groups. The published
`factorHom e h = e⁻¹ (h, 1)` and `awayHom e h' = e⁻¹ (1, h')` embed the two
factors in `G`; they commute elementwise.

The accepted `awayLevelForms R e ι V K'`, for a subgroup `K'` of `H'`,
consists of the functions `f : G → V` with `f (ι γ * g) = f g` and
`f (g * k) = f g` for `k ∈ e⁻¹ (1 × K')`. The accepted `factorTranslation` is
right translation `(h • f) g = f (g * e⁻¹ (h, 1))` by `H` on them. The
accepted `awayTranslate R e ι V c hc`, for `c ∈ H'` with `c⁻¹ * k * c ∈ L` for
`k ∈ K`, maps the forms of level `e⁻¹ (1 × L)` to those of level
`e⁻¹ (1 × K)` by `f ↦ f (· * e⁻¹ (1, c))`.

`CompactOpenLevel H'` is the published category of compact open subgroups of
`H'`. An arrow `a : K ⟶ L` is an element `a.element = c` of `H'` with
`c⁻¹ * k * c ∈ L` for all `k ∈ K` (`a.respects`). The accepted presheaves
`factorFormsPresheaf`, `factorSmoothPresheaf`, `factorExtPresheaf W i`,
`factorAbutmentPresheaf X n`, `factorFiltrationPresheaf X n p` and
`factorGradedPresheaf X n p` are functors out of `(CompactOpenLevel H')ᵒᵖ`.
At `K` their values are the forms of level `e⁻¹ (1 × K)` as a representation
of `H`, their smooth part `A(K)`, `Ext^i(W, A(K))`, `Hom(X, A(K)[n])`, and the
step `F^p` and graded piece `gr^p` of the abutment filtration on it. On an
arrow `a` their map is induced by `awayTranslate` along `a.element`.

For a representation `ρ` of a topological group `C` and compact open levels
`K`, `L`, the published `LevelHecke.heckeOperator ρ K L g : V^L →ₗ V^K` is
`[K g L] v = ∑ ρ (k g) v` over representatives `k` of `K / (K ∩ g L g⁻¹)`
(`HeckeCosets K L g`). The published `LevelHeckeAlgebra R K` is the Hecke
algebra of `K`: the `K`-fixed vectors of `R[C/K]`, with convolution. It acts on
`V^K` by `LevelHecke.heckeAct`, `a • v = ∑_{xK} a(xK) ρ(x) v`. The element
`doubleCoset K g` acts by `[K g K]` (`doubleCoset_smul`).

For an object `X` of a preadditive category, `End X` is Mathlib's
endomorphism ring, with multiplication `f * f' = f' ≫ f`.

## Generic declarations

Namespace `Langlands.Shimura.EquivariantForms`.

- `endRingHom F X : End X →+* End (F.obj X)` for an additive functor `F`:
  `F.map` on endomorphisms (`endRingHom_apply`).

Section `Translation` (universes arbitrary):

- `awayTranslation R e ι V`: the representation of `H'` on the forms of
  trivial level `awayLevelForms R e ι V ⊥` by
  `(h • f) g = f (g * e⁻¹ (1, h))`, the published `rightTranslation` along
  `awayHom e` (`awayTranslation_apply_coe`).
- `factorTranslationIntertwining R e ι V h`: right translation by `h ∈ H` on
  the forms of trivial level, as an intertwining map of `awayTranslation`,
  since the two factors commute.
- `awayFormsFixedEquiv R e ι V K'`: the vectors of `awayTranslation` fixed by a
  subgroup `K'` of `H'` are `R`-linearly equivalent to
  `awayLevelForms R e ι V K'`, by the identity on functions
  (`awayFormsFixedEquiv_apply_coe`, `awayFormsFixedEquiv_symm_apply_coe`).

Section `Hecke` (universes arbitrary; `H'` a topological group). Here `K`,
`L` are compact open levels of `H'` and `g ∈ H'`.

- `awayHecke R e ι V K L g`: the `R`-linear operator `[K g L]` from
  `awayLevelForms R e ι V L` to `awayLevelForms R e ι V K`. It is the published
  `heckeOperator (awayTranslation R e ι V) K L g` transported by
  `awayFormsFixedEquiv`. `awayHecke_apply_coe`:
  `([K g L] f) x = ∑ f (x * e⁻¹ (1, k g))` over `q : HeckeCosets K L g`, with
  `k = q.out`.
- `awayHeckeIntertwining R e ι V K L g`: `awayHecke` as an intertwining map
  between the `factorTranslation` representations at `L` and at `K`; its
  proof is the published `fixedVectorsMap_heckeOperator` applied to
  `factorTranslationIntertwining`.
- `factorHeckeHom R e ι V K L g`: the same as a morphism of `Rep R H` from
  `(factorFormsPresheaf R e ι V).obj (op L)` to the value at `K`.
- `awayHecke_eq_awayTranslate`: if `g⁻¹ * k * g ∈ L` for all `k ∈ K`, then
  `[K g L]` is `awayTranslate` along `g`. The proof writes `[K g L]` as the
  inclusion `[K 1 g L g⁻¹]` after translation by `g`
  (`heckeOperator_eq_comp_translateFixed`, `heckeOperator_one_of_le`).
- `factorFormsPresheaf_map_eq`: for an arrow `a : K ⟶ L`, the map
  `(factorFormsPresheaf R e ι V).map a.op` is
  `factorHeckeHom R e ι V K L a.element`.
- `factorHeckeHom_self`: `[K 1 K]` is the identity.
- `awayHeckeAct R e ι V K a`, `awayHeckeActIntertwining R e ι V K a`: the
  action of `a : LevelHeckeAlgebra R K.subgroup` on
  `awayLevelForms R e ι V K`, the published `heckeAct` of `awayTranslation`
  transported by `awayFormsFixedEquiv`, and the fact that it commutes with
  `factorTranslation` (published `fixedVectorsMap_heckeAct`).
- `formsHeckeAlgebraHom R e ι V K :
  LevelHeckeAlgebra R K.subgroup →+* End ((factorFormsPresheaf R e ι V).obj (op K))`,
  `a ↦ awayHeckeActIntertwining R e ι V K a`. It is a ring homomorphism
  because the action of the Hecke algebra on fixed vectors is a module
  structure (`one_smul`, `mul_smul`, `zero_smul`, `add_smul`).
- `formsHeckeAlgebraHom_doubleCoset`: `doubleCoset K g` maps to
  `factorHeckeHom R e ι V K K g`.

Section `HeckeSmooth` (universes arbitrary; `H`, `H'` topological groups):

- `factorSmoothHeckeHom R e ι V K L g`: `SmoothRep.smoothPartFunctor` applied
  to `factorHeckeHom`, a morphism of smooth representations of `H` between
  the values of `factorSmoothPresheaf` at `L` and at `K`.
- `factorSmoothPresheaf_map_eq`: the map of `factorSmoothPresheaf` along
  `a : K ⟶ L` is `factorSmoothHeckeHom R e ι V K L a.element`.
- `smoothHeckeAlgebraHom R e ι V K`: `formsHeckeAlgebraHom` followed by
  `endRingHom` of the smooth-part functor, a ring homomorphism from the Hecke
  algebra of `K` to `End ((factorSmoothPresheaf R e ι V).obj (op K))`;
  `smoothHeckeAlgebraHom_doubleCoset`.

Section `HeckeExt`: `R`, `G`, `H` and `V` lie in one universe `u`, as the
published smooth `Ext` requires.

- An instance: `SmoothExt.ext R H W i` is additive, from the published
  additivity of right derived functors of the additive functor
  `SmoothHomComplex.homFunctor R H W`.
- `factorExtHecke R e ι V W i K L g`: `Ext^i(W, -)` applied to
  `factorSmoothHeckeHom`, an `R`-linear map from `Ext^i(W, A(L))` to
  `Ext^i(W, A(K))`.
- `factorExtPresheaf_map_eq`: the map of `factorExtPresheaf R e ι V W i`
  along `a : K ⟶ L` is `factorExtHecke R e ι V W i K L a.element`.
- `extHeckeAlgebraHom R e ι V W i K`: the Hecke algebra of `K` acting on
  `Ext^i(W, A(K))`, a ring homomorphism to its endomorphisms in
  `ModuleCat R`; `extHeckeAlgebraHom_doubleCoset`.

Namespace `Langlands.Cohomology.HyperextAbutment`, for a t-structure `t` on a
pretriangulated category `C`:

- `filtrationPostcomp_add`, `gradedPostcomp_add`: the published maps
  `F^p(K, B) →+ F^p(K, B')` and `gr^p(K, B) →+ gr^p(K, B')` of
  postcomposition with `ψ⟦n⟧'` are additive in `ψ`.
- Instances `filtrationFunctor_additive`, `gradedFunctor_additive`: the
  accepted functors `filtrationFunctor t K n p` and `gradedFunctor t K n p`
  are additive.

Back in `Langlands.Shimura.EquivariantForms`, section `HeckeAbutment`, with
`[HasDerivedCategory.{w} (SmoothRep R H)]` and an object `X` of the derived
category of `SmoothRep R H`. The letter `n` is a total degree and `p` a
filtration index.

- `factorAbutmentHecke R e ι V X n K L g`: postcomposition with
  `factorSmoothHeckeHom` (placed in degree `0` and shifted by `n`), from
  `Hom(X, A(L)[n])` to `Hom(X, A(K)[n])`; `factorAbutmentPresheaf_map_eq`;
  `abutmentHeckeAlgebraHom R e ι V X n K` with
  `abutmentHeckeAlgebraHom_doubleCoset`.
- `factorFiltrationHecke R e ι V X n p K L g`: the accepted
  `filtrationFunctor` applied to `factorSmoothHeckeHom` placed in degree `0`,
  from `F^p` at `L` to `F^p` at `K`; `factorFiltrationPresheaf_map_eq`;
  `factorFiltrationHecke_comp_filtrationι` (it commutes with the inclusions
  `F^p ⊆ Hom(X, A(-)[n])`); `filtrationHeckeAlgebraHom R e ι V X n p K`.
- `factorGradedHecke R e ι V X n p K L g`: the same for `gr^p`;
  `factorGradedPresheaf_map_eq`; `factorFiltrationHecke_comp_gradedπ` (it
  commutes with the projections `F^p ⟶ gr^p`);
  `gradedHeckeAlgebraHom R e ι V X n p K`.

The ring homomorphisms to `End` of the abutment, filtration and graded
values are into endomorphisms in `AddCommGrpCat`.

## Harris's case

Namespace `Langlands.Shimura.DefiniteForms`. `A` is a finite-dimensional
`ℚ`-algebra with involution `σ : AlgebraInvolution ℚ A`, and `p : ℕ` with
`hp : p ≠ 0`; `A`, `R` and `V` lie in one universe `u`. `σ.DividingPoints p`
is `GJ(∏_{v ∣ p} ℚ_v)`, `σ.PrimeToPoints p` is `GJ(𝔸_f^{(p)})`, and the
declarations are the generic ones for the published splitting
`e = σ.finiteAdelicPointsSplit p hp` and `ι = σ.finiteAdelicDiagonal`. `K`,
`L` are compact open levels of `GJ(𝔸_f^{(p)})` and `g ∈ GJ(𝔸_f^{(p)})`.

- `dividingSmoothHecke σ p hp R V K L g`, `dividingSmoothPresheaf_map_eq`,
  `dividingSmoothHeckeAlgebraHom σ p hp R V K`: `[K g L]` and the Hecke
  algebra of `K` on the accepted `dividingSmoothPresheaf`, as morphisms of
  smooth representations of `GJ(∏_{v ∣ p} ℚ_v)`.
- `dividingExtHecke σ p hp R V W i K L g`, `dividingExtPresheaf_map_eq`,
  `dividingExtHeckeAlgebraHom σ p hp R V W i K`,
  `dividingExtHeckeAlgebraHom_doubleCoset`: the same on `Ext^i(W, -)` for a
  smooth representation `W` of `GJ(∏_{v ∣ p} ℚ_v)`, the page-2 terms of the
  accepted `dividingSpectralSequence` up to the accepted
  `dividingSecondPageAddEquiv`.
- With `[HasDerivedCategory.{w} (SmoothRep R (σ.DividingPoints p))]`:
  `dividingAbutmentHecke σ p hp R V X n K L g`,
  `dividingAbutmentPresheaf_map_eq`,
  `dividingAbutmentHeckeAlgebraHom σ p hp R V X n K`, and
  `dividingFiltrationHeckeAlgebraHom σ p hp R V X n i K`,
  `dividingGradedHeckeAlgebraHom σ p hp R V X n i K` on the step `F^i` and
  graded piece `gr^i` of the abutment filtration.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4. Worker 61 read the rendered scanned page,
printed p.309 (one-based PDF page 11). Proposition 4.4: "There is a spectral
sequence of `𝒪_m`-modules (4.4.1)
`E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, 𝒪_m(n-1)), 𝒜_ℓ(GJ, 𝓛, K(m))) ⇒
H^{i+j}(S̄_{K(N,m)}, 𝓛~)`. Here `Ext^i` denotes the `i`-th derived functor of
`Hom` in the category of smooth `𝒪_m[GJ]`-modules. Moreover, as
`K(N,m)^p`-varies the spectral sequences are `GG(𝔸_f^p)`-equivariant."

How the module relates to Harris (an explanation, not formalized):

- Equivariance at a fixed level. The accepted `DefiniteFormsSmoothExt` reads
  "as `K(N,m)^p` varies" as a presheaf on compact open levels `K` of
  `GJ(𝔸_f^{(p)})`. Its arrows are inclusions of levels and translations by
  elements `g` with `g⁻¹ K g ⊆ L`. For the forms, the `GJ(𝔸_f^{(p)})`-module
  of all levels at once is the union of the forms of all levels. Its
  `K`-invariants are the forms of level `K`. On these invariants, the
  equivariance is the action of the double-coset operators `[K g L]` for all
  `g`, and of the Hecke algebra of `K`. This module defines these operators on
  each term of the accepted presheaves. On the terms `Ext^i(W, A(K))`, the
  abutment and its filtration, they are defined by functoriality of the term
  in `A(K)`, not from a `GJ(𝔸_f^{(p)})`-action on a limit or colimit over the
  levels.
- Compatibility with the presheaves. `factorFormsPresheaf_map_eq` and its
  analogues show that the maps of the presheaves along arrows are the
  operators `[K g L]` of the arrow's element. So the operators extend the
  equivariance of `DefiniteFormsSmoothExt` from the arrows to all double
  cosets.
- Which Hecke algebra. The operators and the Hecke algebra are the published
  `LevelHecke.heckeOperator`, `LevelHeckeAlgebra` and `heckeAct`, for the
  representation `awayTranslation` of `GJ(𝔸_f^{(p)})` on forms of trivial
  level. `awayFormsFixedEquiv` identifies its `K`-fixed vectors with the forms of
  level `e⁻¹ (1 × K)`, by the identity on functions. Since all values are
  taken through these published constructions, the Hecke algebras here are
  the same objects as the ones in the published level-Hecke modules.
- Hecke operators on the spectral sequence. Harris's statement asserts
  equivariance of the spectral sequences, including their differentials. This
  module provides the operators on the page-2 terms (`dividingExtHecke`,
  through the accepted `dividingSecondPageAddEquiv`) and on the abutment, its
  filtration steps and graded pieces, and their compatibility with the
  inclusions `F^p ⊆ Hom(X, A(K)[n])` and projections `F^p ⟶ gr^p`. It does not
  show that the differentials of the spectral sequence, or the identification
  of page 2, commute with them.
- The group `GG(𝔸_f^p)`. As in `DefiniteFormsSmoothExt`, we work with
  `GJ(𝔸_f^{(p)})` directly. The identification of `GG(𝔸_f^p)` with
  `GJ(𝔸_f^p)` that Harris uses is not formalized.
- All declarations are ours, derived from Mathlib and the published and
  accepted modules named above. `awayTranslation`, `awayFormsFixedEquiv`,
  `awayHecke` and the `*Hecke*` maps and ring homomorphisms are internal
  constructions not printed in Harris 1999. `endRingHom` and the additivity
  lemmas and instances are general facts used to build the ring
  homomorphisms.

## Related declarations

- Library `Langlands.Shimura.LevelHecke.heckeActionNatTrans`
  (`Shimura/LevelHeckeAction`): the double-coset operators as a natural
  transformation of fixed-vector functors on smooth representations of `C`
  carrying an action of a monoid `Γ` by morphisms of smooth representations.
  Here the representation of the
  second factor is on forms of trivial level, which are not assumed smooth
  for that factor. So the operators are taken directly from `heckeOperator`
  and `heckeAct`, and their commuting with the first factor is
  `awayHeckeIntertwining`.
- `Langlands.Shimura.EquivariantForms.coefficientSmoothPresheaf`
  (`Shimura/DefiniteFormsSmoothCoefficients`, accepted, not yet in the
  Library): the case of Proposition 4.10 with coefficients. Hecke operators
  for it are not treated here.

## Scope

The module provides the double-coset operators `[K g L]` and the Hecke
algebra of `K` acting on the forms with trivial coefficients, their smooth
parts, their `Ext` groups, and the intended abutment of the hyperext
spectral sequence with its filtration steps and graded pieces. It shows that
the maps of the accepted presheaves along arrows of levels are these
operators. It does not:

- prove that the operators commute with the differentials of the spectral
  sequence or with `factorSecondPageAddEquiv`;
- prove composition laws for the operators `[K g L]` between different
  levels beyond those implied by the ring homomorphisms at one level;
- treat forms with coefficients (Proposition 4.10), the limit over `m`, or
  any Galois action;
- construct `M̌_N`, the Shimura varieties or their cohomology, or prove
  convergence or the comparison with `H^{i+j}(S̄_{K(N,m)}, 𝓛~)`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published and accepted modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
