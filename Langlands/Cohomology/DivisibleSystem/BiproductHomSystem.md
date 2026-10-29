# Finite direct sums of Hom complexes and of Hom-complex systems

Author: Worker 61. Built on `Langlands.Cohomology.LinearHomComplex`
(`LinearHomComplex.complex`, the Hom complex of two cochain complexes as a
complex of `R`-modules, and `LinearHomComplex.map`, its functoriality by
precomposition and postcomposition, with `map_f_apply`, `map_id` and
`map_comp`), on `Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`,
`DivisibleSystem.obj`, `DivisibleSystem.projection`, `powSMul`,
`comp_powSMul`, `powSMul_comp_powSMul`, `shortComplex_exact_congr`,
`SmoothRepComplexDivisibleSystem`), on
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`cochainTransition`,
`cochainTransition_eq_iff`, `cochainTransition_v`,
`projection_comp_homTransition`, `homComplexTransition`,
`homComplexSystem`, `homComplexLimit`, `smoothHomComplexSystem`) and on
`Langlands.Cohomology.DivisibleSystem.AdjunctionHomSystem`
(`compactInductionSystem`, `restrictionSystem`,
`smoothHomComplexSystemReciprocityIso`). From Mathlib it uses the biproduct
API of `Mathlib.CategoryTheory.Preadditive.Biproducts` and
`Mathlib.CategoryTheory.Limits.Shapes.Biproducts` (`biproduct.lift`,
`biproduct.desc`, `biproduct.map`, `biproduct.mapIso`, `biproduct.lift_desc`,
`biproduct.total`, `biproduct.ι_π_self`, `biproduct.ι_π_ne`,
`biproduct.hom_ext`, `biproduct.hom_ext'`, the instances making a biproduct of
monomorphisms a monomorphism and a biproduct of epimorphisms an epimorphism,
and `Abelian.hasFiniteBiproducts`), `ShortComplex.homologyFunctor`,
`ShortComplex.exact_iff_isZero_homology`, `limMap`, `limit.hom_ext`,
`HasLimit.isoOfNatIso`, `NatIso.ofComponents` and the Hom-complex API
`CochainComplex.HomComplex` (`Cochain.ext`, `Cochain.ofHom`, composition of
cochains).

Except for the first constructions on levelwise biproducts of functors
(`biproductSystem` up to `biproductSystemι_app`), the index type `ι` of a
direct sum is finite (`[Finite ι]`) and lives in `Type`, as required by
Mathlib's `biproduct.total` and `biproduct.lift_desc`.

## Hom complexes out of a finite biproduct (namespace `Langlands.Cohomology.LinearHomComplex`)

`R : Type w` is a ring and `C` an `R`-linear preadditive category with
Hom-universe `v`; `LinearHomComplex.complex R P Q` is the complex of
`R`-modules (in `ModuleCat.{v} R`) of cochains from `P` to `Q`.

- `map_add_left`, `map_zero_left`, `map_sum_left`: the chain map
  `map R f g` is additive in `f` (`map R (f₁ + f₂) g = map R f₁ g + map R f₂ g`,
  `map R 0 g = 0`, and it commutes with finite sums `∑ i ∈ s, f i`). The first
  two are checked on the cochain components `f.f p ≫ z.v p q hpq ≫ g.f q`
  given by `map_f_apply`; the third follows from the first by `map_sum`.
- `sourceBiproductIso R K L : complex R (⨁ K) L ≅ ⨁ i, complex R (K i) L`
  for a finite family of cochain complexes `K i` with a biproduct `⨁ K` and a
  cochain complex `L`. The `i`-th component of the map is precomposition with
  the inclusion `biproduct.ι K i : K i ⟶ ⨁ K` (`map R (biproduct.ι K i) (𝟙 L)`);
  the restriction of the inverse to the `i`-th summand is precomposition with
  the projection `biproduct.π K i`. The biproduct on the right is in the
  abelian category `CochainComplex (ModuleCat R) ℤ`. Proof: the composite
  `hom ≫ inv` is `∑ i, map R (π i ≫ ι i) (𝟙 L) = map R (∑ i, π i ≫ ι i) (𝟙 L)`,
  which is the identity by `biproduct.total` and `map_id`; the composite
  `inv ≫ hom` has components `map R (ι j ≫ π i) (𝟙 L)`, which is the identity
  for `i = j` and zero otherwise by `biproduct.ι_π_self`, `biproduct.ι_π_ne`
  and `map_zero_left`.
- `sourceBiproductIso_hom_π` and `ι_sourceBiproductIso_inv` (`simp`, with
  `reassoc` forms) state these components.

## Finite biproducts of short complexes (namespace `Langlands.Cohomology`)

`C` is an abelian category.

- `biproductShortComplex S`: for a finite family `S i` of short complexes,
  the short complex `⨁ᵢ (S i).X₁ ⟶ ⨁ᵢ (S i).X₂ ⟶ ⨁ᵢ (S i).X₃` with the
  biproducts of the maps (`biproduct.map`). `biproductShortComplexπ S i` and
  `biproductShortComplexι S i` are the morphisms of short complexes given by
  the biproduct projections and inclusions.
- `exact_biproductShortComplex S h`: if every `S i` is exact, so is
  `biproductShortComplex S`. Proof: the identity of `biproductShortComplex S`
  is `∑ i, biproductShortComplexπ S i ≫ biproductShortComplexι S i`
  (componentwise `biproduct.total`). The homology functor of short complexes
  is additive, so the identity of the homology is the sum of the maps on
  homology of these composites; each of them factors through the homology of
  `S i`, which is zero. Hence the homology is zero, i.e. the short complex is
  exact.
- `shortExact_biproductShortComplex S h`: if every `S i` is short exact, so
  is `biproductShortComplex S`: exactness by the previous lemma, and the
  biproduct of monomorphisms (epimorphisms) is a monomorphism (epimorphism) by
  Mathlib's instances.

## Levelwise biproducts of functors

`J` is a category and `D` a category with zero morphisms and biproducts of
shape `ι` (for the first four items `ι : Type*` need not be finite).

- `biproductSystem F : J ⥤ D` (an `abbrev`): for a family of functors
  `F i : J ⥤ D`, the functor `j ↦ ⨁ᵢ (F i).obj j` with maps
  `biproduct.map fun i => (F i).map φ`. `biproductSystem_obj` and
  `biproductSystem_map` state this (by definition).
- `biproductSystemMap α` and `biproductSystemMapIso e`: a family of natural
  transformations (isomorphisms) `F i ⟶ F' i` induces one between the
  levelwise biproducts, with components `biproduct.map` (`biproduct.mapIso`)
  of the components; `biproductSystemMap_app` and `biproductSystemMapIso_hom`
  state this (by definition).
- `biproductSystemπ F i : biproductSystem F ⟶ F i` and
  `biproductSystemι F i : F i ⟶ biproductSystem F`: the levelwise biproduct
  projections and inclusions (`biproductSystemπ_app`, `biproductSystemι_app`).
- `limitBiproductSystemIso F : limit (biproductSystem F) ≅ ⨁ᵢ limit (F i)`,
  for `D` preadditive, `ι : Type` finite and limits of shape `J` in `D`:
  limits commute with finite biproducts. The `i`-th component of the map is
  `limMap (biproductSystemπ F i)`, and the restriction of the inverse to the
  `i`-th summand is `limMap (biproductSystemι F i)`
  (`limitBiproductSystemIso_hom_π`, `ι_limitBiproductSystemIso_inv`, `simp`
  with `reassoc` forms). Proof: after composing with the limit projections,
  `hom ≫ inv` is the identity by `biproduct.total` at each `j`, and
  `inv ≫ hom` has components the identity or zero by `biproduct.ι_π_self` and
  `biproduct.ι_π_ne` at each `j`.

## Direct sums of `ℓ`-divisible systems (namespace `Langlands.Cohomology.DivisibleSystem`)

`C` is an abelian category. An `ℓ`-divisible system `T` (Harris 1999, (2.1),
the published `DivisibleSystem C ℓ`) consists of an inverse system
`T.tower : ℕᵒᵖ ⥤ C` (objects `T m`, maps `j`), maps `i : T m' ⟶ T m` for
`m' < m`, and the exactness and torsion conditions of the structure.

- `powSMul_biproduct X m`: multiplication by `ℓ ^ m` on `⨁ X` is the
  biproduct of the multiplications by `ℓ ^ m` on the summands (componentwise
  `comp_powSMul`).
- `biproduct T` (an `abbrev`): for a finite family `T i` of `ℓ`-divisible
  systems, the `ℓ`-divisible system with `tower := biproductSystem` of the
  towers and `inclusion h := biproduct.map` of the inclusions. The axioms are
  checked summandwise: `ℓ ^ m` kills `⨁ᵢ T i m` by `powSMul_biproduct`; the
  composite of `i` and `j` vanishes componentwise; the short exact sequences
  `T m' ⟶ T m ⟶ T (m - m')` are biproducts of short exact sequences
  (`shortExact_biproductShortComplex`); the torsion and flatness exactness
  conditions are biproducts of exact short complexes
  (`exact_biproductShortComplex`), after rewriting multiplication by powers of
  `ℓ` with `powSMul_biproduct` (`shortComplex_exact_congr`).
  `biproduct_tower` and `biproduct_inclusion` state the data (by definition).
- `biproductι T i : T i ⟶ biproduct T` and `biproductπ T i : biproduct T ⟶ T i`:
  the inclusion and projection as morphisms of `ℓ`-divisible systems (natural
  transformations of the towers commuting with the inclusions `i`), with
  components the biproduct inclusions and projections
  (`biproductι_tower_app`, `biproductπ_tower_app`, `simp`).

## Precomposition on Hom-complex systems

`R : Type w` is a ring, `C` an `R`-linear abelian category, and `T`, `T'`,
`W` are `ℓ`-divisible systems of `ℤ`-graded cochain complexes in `C`.
`homComplexSystem R T W` is the published inverse system
`m ↦ Hom^•(T m, W m)` with transitions `homComplexTransition` (Harris's maps
(4.10.3)).

- `cochainTransition_ofHom_comp W α h z`: for a morphism of inverse systems
  `α : T'.tower ⟶ T.tower` (compatibility with the inclusions is not needed),
  the transition of `Cochain.ofHom (α_m) ∘ z` from level `m` to level `m'` is
  `Cochain.ofHom (α_m') ∘` the transition of `z`. Proof: by
  `cochainTransition_eq_iff` it suffices to compare the composites with the
  projections of `T'` and `W`; componentwise this is the naturality of `α`
  and `projection_comp_homTransition`.
- `map_comp_homComplexTransition R W α h`: the same statement for the chain
  maps `LinearHomComplex.map R (α_m) (𝟙 (W m))` and `homComplexTransition`.
- `homComplexSystemPrecomp R W α : homComplexSystem R T W ⟶
  homComplexSystem R T' W`: the morphism of inverse systems with level `m`
  component `LinearHomComplex.map R (α_m) (𝟙 (W m))` (precomposition by `α_m`),
  natural by the previous lemma.

## Hom-complex systems out of a direct sum

`T i` is a finite family of `ℓ`-divisible systems of cochain complexes and `W`
an `ℓ`-divisible system of cochain complexes.

- `homComplexSystemBiproductIso R T W : homComplexSystem R (biproduct T) W ≅
  biproductSystem fun i => homComplexSystem R (T i) W`: at level `m` it is
  `LinearHomComplex.sourceBiproductIso R (fun i => T i m) (W m)`. Naturality:
  after composing with the biproduct projections, the `i`-th component is
  `map_comp_homComplexTransition` for `α = (biproductι T i).tower`.
  `homComplexSystemBiproductIso_hom_app_π` (`simp`, with a `reassoc` form)
  states that the `i`-th component at level `m` is the level `m` component of
  `homComplexSystemPrecomp R W (biproductι T i).tower`.
- `homComplexLimitBiproductIso R T W : homComplexLimit R (biproduct T) W ≅
  ⨁ᵢ homComplexLimit R (T i) W`: `HasLimit.isoOfNatIso` of the previous
  isomorphism followed by `limitBiproductSystemIso`.
  `homComplexLimitBiproductIso_hom_π` states that its `i`-th component is
  `limMap (homComplexSystemPrecomp R W (biproductι T i).tower)`, the map of
  inverse limits induced by precomposition with the inclusions.

## Compact induction from several open subgroups (namespace `Langlands.Cohomology`)

`R : Type u` is a commutative ring, `G : Type u` a topological group,
`H : ι → Subgroup G` a finite family of subgroups with
`hH : ∀ i, IsOpen (H i : Set G)`, `T i` an `ℓ`-divisible system of cochain
complexes of smooth representations of `H i`
(`SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ`) and `W` one of smooth
representations of `G`. `compactInductionSystem R (hH i) (T i)` is the
published `ℓ`-divisible system `m ↦ c-Ind_{H i}^G (T i m)` and
`restrictionSystem R (hH i) W` is `m ↦ W m|_{H i}`.

- `smoothHomComplexSystemBiproductReciprocityIso R hH T W`:
  `smoothHomComplexSystem R G (biproduct fun i => compactInductionSystem R (hH i) (T i)) W ≅
  biproductSystem fun i => smoothHomComplexSystem R (H i) (T i) (restrictionSystem R (hH i) W)`,
  i.e. `m ↦ Hom^•_G(⨁ᵢ c-Ind_{H i}^G (T i m), W m)` is isomorphic to
  `m ↦ ⨁ᵢ Hom^•_{H i}(T i m, W m|_{H i})`. It is
  `homComplexSystemBiproductIso` followed by `biproductSystemMapIso` of the
  published Frobenius reciprocity isomorphisms
  `smoothHomComplexSystemReciprocityIso R (hH i) (T i) W`.
- `smoothHomComplexLimitBiproductReciprocityIso R hH T W`: the induced
  isomorphism `homComplexLimit R (biproduct fun i => compactInductionSystem R (hH i) (T i)) W ≅
  ⨁ᵢ homComplexLimit R (T i) (restrictionSystem R (hH i) W)`
  (`HasLimit.isoOfNatIso` followed by `limitBiproductSystemIso`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999).

Proof of Proposition 4.4, printed p.310 (one-based PDF page 12): "Let `O_i`
be the set of `GJ` orbits on `BT(i) × Δ` (notation as on p. 93 of [H1], where
this was denoted `𝒪_i`). Since (recalling that `ẽ = (e, …, δ)`) (4.4.4)
`Z^{i,j} = ⊕_{dim(e)=n−1−i} C^j(ẽ) = ⊕_{(e,δ) ∈ O_i} c-Ind_{S(ẽ)}^{GJ} C^j(ẽ)`
is a sum of compactly induced modules, the argument goes through as before."

Proof of Proposition 4.10, printed p.311 (one-based PDF page 13): "We need to
check that the complexes used to obtain the spectral sequences (4.9) satisfy
a Mittag-Leffler condition as m varies. By (4.4.4) and (4.8), these are of
the form `⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ) ∈ O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ),
Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`, which can be rewritten (4.10.2)
`⊕_{i+j=k} ⊕_{(e,δ) ∈ O_{-i}} Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ),
Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`."

Harris does not spell out the rewriting. It consists of two steps: Hom out of
the direct sum over `(e, δ) ∈ O_{-i}` is the direct sum of the Hom modules,
and Hom out of a compact induction `c-Ind_{S(ẽ)}^{GJ}` is Hom out of the
inducing `S(ẽ)`-module (Frobenius reciprocity for compact induction from the
open subgroup `S(ẽ)`). The second step is the published module
`AdjunctionHomSystem`; this module formalizes the first step for Hom
complexes and for the inverse systems over `m` of Hom complexes of
`ℓ`-divisible systems formed in the published HomSystem module, and combines
both steps in `smoothHomComplexSystemBiproductReciprocityIso` for a single
degree `-i`, with the index set `O_{-i}` and `H i = S(ẽ)`. The direct sum of
`ℓ`-divisible systems, the general biproduct statements (Hom complexes,
short complexes, levelwise biproducts and their limits) and all proofs are
ours.

The Lean statements require the index type to be finite: Mathlib's
biproducts are finite, and Hom out of an infinite direct sum is a product
rather than a direct sum. Harris writes the sum over `O_{-i}` as a direct sum
on both sides of the rewriting and does not discuss its finiteness on these
pages; this module does not prove that `O_{-i}` is finite.

## Scope

The module does not identify Harris's complexes (4.10.2), the modules
`C^j_m(ẽ)`, the orbit sets `O_{-i}` or the coefficients
`Hom(𝒪_m[K_p/H_p]^M, 𝓛_m)` with the objects constructed here. It does not
treat the passage from `K_p/H_p` to `C_p/H_p` in the coefficients, the total
complex over `i + j = k`, or Harris's Mittag-Leffler argument. It does not
compare the isomorphisms with the inclusions of the `ℓ`-divisible systems or
with cohomology, Ext groups or the spectral sequences.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
