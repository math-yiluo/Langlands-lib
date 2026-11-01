# Čech cohomology computes actual `R`-module cohomology

Author: Worker 207.

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution`. For `π : X ⟶ Spec R` separated, a finite
ordered affine cover `𝒰` of `X` and a quasi-coherent `𝒪_X`-module `M`, it identifies the
homology of the alternating Čech cochain complex with the actual `R`-module cohomology of `M`
in every degree, and in degree one also with Čech `H¹` computed from cochains indexed by all
ordered pairs of cover indices, whose cocycles and coboundaries are exactly the Library's
`CechDegreeOne.IsCocycle` and `CechDegreeOne.IsCoboundary`:

```lean
def cechCohomologyIso (n : ℕ) :
    (cechCochainComplex π 𝒰 M).homology n ≅ (relativeCohomology π n).obj M

def cechH1Equiv :
    (OModulePresheaf.ofModules π M).HSucc 𝒰 0 ≃ₗ[R] (relativeCohomology π 1).obj M

def allPairsH1Equiv :
    AllPairsH1 (OModulePresheaf.ofModules π M) 𝒰 ≃ₗ[R] (relativeCohomology π 1).obj M
```

Here `R : CommRingCat.{u}`, `X : Scheme.{u}`, and the last two declarations and
`cechCohomologyIso` assume `[IsSeparated π]` and `[M.IsQuasicoherent]`.
`DerivedSections.relativeCohomology π n` is the Library's actual cohomology functor
`(relativeGlobalSections π).rightDerived n : X.Modules ⥤ ModuleCat R`, the right derived functor
of global sections regarded as `R`-modules through `π`.

## Imported interface

- From the Library's port of the Anthropic FLT source
  (`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`, namespace
  `AlgebraicGeometry`): `𝒰.Idx i` is the type of strictly increasing maps
  `Fin (i + 1) → 𝒰.ι`, `𝒰.inter s = ⨅ j, 𝒰.U (s.1 j)`, `𝒰.face s j` deletes the `j`-th index;
  for `F : OModulePresheaf ρ`, `F.cochain 𝒰 i = ∀ s : 𝒰.Idx i, F.obj (𝒰.inter s)`, `F.d 𝒰 i` is
  the alternating Čech differential (`d_apply`: `F.d 𝒰 i c s` is the sum over `j` of
  `(-1)^j • F.res _ (c (𝒰.face s j))`), and
  `F.HSucc 𝒰 i = ker (F.d 𝒰 (i + 1)) ⧸ (range (F.d 𝒰 i)).comap (subtype)`.
  `OModulePresheaf.ofModules π M` has objects `Γ(M, U)`, the `R`-module structure through `π`
  and the restriction maps of `M`.
- From `CechResolution.Comparison`: `cechCochainComplex π 𝒰 M`, the `ℕ`-indexed complex of
  `R`-modules `CochainComplex.of` the modules `(ofModules π M).cochain 𝒰 i` and the maps
  `(ofModules π M).d 𝒰 i`, and `sectionsComplexIso π 𝒰 M`, the isomorphism from
  `relativeGlobalSections π` applied to the sheafified Čech resolution `cechComplex 𝒰 M` to
  `cechCochainComplex π 𝒰 M`. From `CechResolution.Exact`, `CechResolution.Acyclic`:
  `quasiIso_cechAug` (the augmentation `cechAug 𝒰 M : M[0] ⟶ cechComplex 𝒰 M` is a
  quasi-isomorphism) and `isZero_relativeCohomology_cechTerm` (its terms are acyclic for
  `relativeGlobalSections π`, using `IsSeparated π` and quasi-coherence).
- From `Langlands.Cohomology.AcyclicResolution`: `resolutionComparison F ε n`, the comparison
  from the `n`-th homology of `F` applied to a right resolution `ε : A[0] ⟶ K` to
  `(F.rightDerived n).obj A`, computed with Mathlib's chosen injective resolution and the lift
  `lift ε (𝟙 A) _` (`comp_lift_id`), and the proved statement
  `acyclicResolutionComparisonStatement` (for a quasi-isomorphism `ε` into `F`-acyclic terms,
  this comparison is an isomorphism in every degree).
- From `CechDegreeOne`: for `z : ∀ a b, Γ(G, Z a ⊓ Z b)`, `IsCocycle Z z` says
  `res (z a b) + res (z b c) = res (z a c)` on every open `O ≤ Z a ⊓ Z b`, `O ≤ Z b ⊓ Z c`,
  `O ≤ Z a ⊓ Z c`; `IsCoboundary Z z` says `z a b = res (g b) - res (g a)` for some
  `g : ∀ a, Γ(G, Z a)`; `isQuasicoherent_unit X` (the unit sheaf of modules is quasi-coherent).
- `Langlands.Scheme.Modules.structureSheaf Y` (from `Modules.Tensor`) is by definition
  `SheafOfModules.unit Y.ringCatSheaf`; `Scheme.OrderedAffineCover.ofCompactSpace X` (from
  `OrderedAffineCoverCompact`) is a finite ordered affine cover of a quasi-compact scheme.

## Declarations

### Čech cohomology and actual cohomology (section `Comparison`)

- `cechHomologyOneEquiv π 𝒰 M` (no separatedness or quasi-coherence assumption): the
  `R`-linear equivalence `(cechCochainComplex π 𝒰 M).homology 1 ≃ₗ[R] (ofModules π M).HSucc 𝒰 0`.
  Proof: the differentials `0 → 1` and `1 → 2` of the complex are `ofHom (d 𝒰 0)` and
  `ofHom (d 𝒰 1)` (`CochainComplex.of_d`), so `K.sc' 0 1 2` is isomorphic (`ShortComplex.isoMk`
  with identities) to `ModuleCat.shortComplexOfCompEqZero (d 𝒰 0) (d 𝒰 1)`; compose
  `homologyIsoSc' 0 1 2`, the induced homology isomorphism, Mathlib's `moduleCatHomologyIso`
  (homology as `ker g ⧸ range (codRestrict f)`), and `Submodule.quotEquivOfEq` with
  `LinearMap.range_codRestrict` to reach the quotient `HSucc 𝒰 0`.
- `isIso_resolutionComparison_cechAug π 𝒰 M n` (from here on with `[IsSeparated π]`,
  `[M.IsQuasicoherent]`): `resolutionComparison (relativeGlobalSections π) (cechAug 𝒰 M) n` is an
  isomorphism. Proof: the second component of `acyclicResolutionComparisonStatement` applied to
  `cechAug 𝒰 M` (`quasiIso_cechAug`, made a local instance), the acyclicity
  `isZero_relativeCohomology_cechTerm`, Mathlib's chosen injective resolution of `M` and the lift
  of `comp_lift_id`.
- `cechCohomologyIso π 𝒰 M n`: the isomorphism of `R`-modules
  `(cechCochainComplex π 𝒰 M).homology n ≅ (relativeCohomology π n).obj M`: the homology of the
  inverse of `sectionsComplexIso`, followed by the isomorphism of the previous item.
- `cechH1Equiv π 𝒰 M`: `(cechHomologyOneEquiv π 𝒰 M).symm` followed by `cechCohomologyIso` in
  degree `1`, as an `R`-linear equivalence `(ofModules π M).HSucc 𝒰 0 ≃ₗ[R] H¹`.

### A combinatorial lemma

- `add_eq_of_strict r h0 hs h a b c`: for a family `r a b` in an additive commutative group
  indexed by a linear order, with `r a a = 0`, `r b a = -r a b`, and `r a b + r b c = r a c`
  whenever `a < b < c`, the identity `r a b + r b c = r a c` holds for all `a`, `b`, `c`. Proof:
  dispose of the cases with equal indices, then check the six orderings of three distinct
  indices with `abel`.

### All-pairs and alternating Čech `1`-cochains (section `AllPairs`)

Here `F : OModulePresheaf ρ` is an arbitrary presheaf of modules over `ρ : V ⟶ Spec (.of S)`,
`S : Type u` a commutative ring, and `𝒰 : V.OrderedAffineCover`.

- `singleIdx 𝒰 a`, `pairIdx 𝒰 h`, `tripleIdx 𝒰 hab hbc`: the indices `(a)`, `(a, b)` for
  `h : a < b`, and `(a, b, c)` for `a < b < c`, in `𝒰.Idx 0`, `𝒰.Idx 1`, `𝒰.Idx 2`.
  `le_inter_singleIdx`, `le_inter_pairIdx`: `𝒰.U a ≤ 𝒰.inter (singleIdx 𝒰 a)` and
  `𝒰.U a ⊓ 𝒰.U b ≤ 𝒰.inter (pairIdx 𝒰 h)`; `inter_le_pair s`:
  `𝒰.inter s ≤ 𝒰.U (s.1 0) ⊓ 𝒰.U (s.1 1)`. `res_cochain_congr`: restrictions to an open `O` of
  the components of a cochain at equal indices agree.
- `AllPairsCochain F 𝒰 = ∀ a b : 𝒰.ι, F.obj (𝒰.U a ⊓ 𝒰.U b)`: Čech `1`-cochains indexed by all
  ordered pairs.
- `allPairsCocycles F 𝒰`: the `S`-submodule of cochains `z` with
  `F.res h₁ (z a b) + F.res h₂ (z b c) = F.res h₃ (z a c)` for all `a b c` and every open `O`
  with `h₁ : O ≤ U a ⊓ U b`, `h₂ : O ≤ U b ⊓ U c`, `h₃ : O ≤ U a ⊓ U c`.
- `allPairsD0 F 𝒰`: the `S`-linear map `g ↦ (a b ↦ F.res _ (g b) - F.res _ (g a))` from families
  `g : ∀ a, F.obj (𝒰.U a)` (`allPairsD0_apply`). `allPairsCoboundaries F 𝒰` is its range;
  `allPairsD0_mem_allPairsCocycles` and `allPairsCoboundaries_le` (coboundaries are cocycles,
  by `F.res_res`).
- `AllPairsH1 F 𝒰`: the quotient of `allPairsCocycles F 𝒰` by the coboundaries pulled back along
  the inclusion.
- `allPairs_self`, `allPairs_swap`: a cocycle satisfies `z a a = 0` (take `a = b = c` and
  `O = U a ⊓ U a`) and `z a b = -F.res _ (z b a)` (take `c = a` and `O = U a ⊓ U b`).
- `toAlternating F 𝒰`: the `S`-linear map sending `z` to the alternating cochain
  `s ↦ F.res _ (z (s.1 0) (s.1 1))` (`toAlternating_apply`).
- `ofAlternating F 𝒰`: the `S`-linear map sending an alternating cochain `c` to the all-pairs
  cochain equal to (the restriction of) `c (a, b)` for `a < b`, to `-c (b, a)` for `b < a` and to
  `0` for `a = b` (`ofAlternating_apply_of_lt`, `ofAlternating_apply_of_gt`,
  `ofAlternating_self`).
- `toAlternating_ofAlternating` (for every cochain) and `ofAlternating_toAlternating` (for every
  all-pairs cocycle, using `allPairs_self` and `allPairs_swap`): the two maps are mutually
  inverse there.
- `d_toAlternating`: `F.d 𝒰 1` kills `toAlternating F 𝒰 z` for a cocycle `z` (expand `d_apply`
  with `Fin.sum_univ_three` and use the cocycle identity on `𝒰.inter t`).
- `res_d_tripleIdx`: the restriction to `O` of `F.d 𝒰 1 w` at `(a, b, c)` is
  `w (b, c) - w (a, c) + w (a, b)` restricted to `O`.
- `ofAlternating_mem_allPairsCocycles`: if `F.d 𝒰 1 w = 0` then `ofAlternating F 𝒰 w` is an
  all-pairs cocycle. Proof: for an open `O`, apply `add_eq_of_strict` to the family indexed by
  the linearly ordered subtype `{x // O ≤ 𝒰.U x}`, `r x y = F.res _ (ofAlternating F 𝒰 w x y)`;
  vanishing on the diagonal and antisymmetry follow from the defining cases, and the strict
  case `x < y < z` is `res_d_tripleIdx` with `F.d 𝒰 1 w = 0`.
- `alternatingEquiv F 𝒰`: the `S`-linear equivalence
  `allPairsCocycles F 𝒰 ≃ₗ[S] LinearMap.ker (F.d 𝒰 1)` given by `toAlternating` and
  `ofAlternating` (`alternatingEquiv_apply_coe`, `alternatingEquiv_symm_apply_coe`).
- `toCochainZero F 𝒰`: the `S`-linear map from families `g : ∀ a, F.obj (𝒰.U a)` to alternating
  `0`-cochains, `s ↦ F.res _ (g (s.1 0))` (`toCochainZero_apply`); it is surjective
  (`toCochainZero_surjective`, using `singleIdx`), and
  `F.d 𝒰 0 (toCochainZero F 𝒰 g) = toAlternating F 𝒰 (allPairsD0 F 𝒰 g)` (`d_toCochainZero`).
- `mem_allPairsCoboundaries_iff_toAlternating`: a cocycle `z` is an all-pairs coboundary iff
  `toAlternating F 𝒰 z` lies in the range of `F.d 𝒰 0`.
- `allPairsH1EquivHSucc F 𝒰`: the `S`-linear equivalence `AllPairsH1 F 𝒰 ≃ₗ[S] F.HSucc 𝒰 0`
  induced by `alternatingEquiv` on the quotients (`Submodule.Quotient.equiv`; the submodules
  correspond by the previous item).

### All-pairs Čech cocycles of a module (section `OfModules`)

- `mem_allPairsCocycles_ofModules_iff π 𝒰 M z`: for `F = OModulePresheaf.ofModules π M`,
  `z ∈ allPairsCocycles F 𝒰 ↔ CechDegreeOne.IsCocycle (G := M) 𝒰.U z` (by `Iff.rfl`).
- `mem_allPairsCoboundaries_ofModules_iff π 𝒰 M z`:
  `z ∈ allPairsCoboundaries F 𝒰 ↔ CechDegreeOne.IsCoboundary (G := M) 𝒰.U z`.
- `allPairsH1Equiv π 𝒰 M` (with `[IsSeparated π]`, `[M.IsQuasicoherent]`):
  `allPairsH1EquivHSucc` followed by `cechH1Equiv`, an `R`-linear equivalence from
  `AllPairsH1 (ofModules π M) 𝒰` to `(relativeCohomology π 1).obj M`.
- `allPairsH1Map π 𝒰 M`: the `R`-linear map from `allPairsCocycles (ofModules π M) 𝒰` to
  `(relativeCohomology π 1).obj M` sending a cocycle to the image of its class.
  `allPairsH1Map_surjective`: it is surjective. `allPairsH1Map_eq_zero_iff z`:
  `allPairsH1Map π 𝒰 M z = 0 ↔ CechDegreeOne.IsCoboundary (G := M) 𝒰.U z.1`.

### The structure sheaf and finite affine covers

- The imported instance `CechDegreeOne.isQuasicoherent_unit Y` supplies quasi-coherence of
  `Langlands.Scheme.Modules.structureSheaf Y`, which is `SheafOfModules.unit Y.ringCatSheaf`.
- `orderedAffineCoverOfQuasiCompact π` (for `[QuasiCompact π]`, `π : X ⟶ Spec R`):
  `Scheme.OrderedAffineCover.ofCompactSpace X`, using that `X` is quasi-compact because `Spec R`
  is (`QuasiCompact.compactSpace_of_compactSpace`).

For example, for a field `k` and an abelian scheme `A` over `Spec (.of k)`, the proper morphism
`A.X.hom` is separated and quasi-compact, so `allPairsH1Equiv A.X.hom
(orderedAffineCoverOfQuasiCompact A.X.hom) (structureSheaf A.X.left)` is a `k`-linear
equivalence from all-pairs Čech `H¹` of `𝒪_A` to `(relativeCohomology A.X.hom 1).obj
(structureSheaf A.X.left)`.

## Provenance

Derived. The content is the degree-one and general cases of standard comparisons in the Stacks
Project, all from the registered folder `stacks-flasque-affine-vanishing-kunneth-a04446e5`
(Stacks commit `a04446e57ec1fbc252a871afcec7752fb2807b14`):

- `cechCohomologyIso`: Cohomology of Schemes, Lemma `lemma-cech-cohomology-quasi-coherent`
  (tag 01XD, `coherent.tex` line 246), `Ȟ^p(𝒰, F) = H^p(X, F)` for a quasi-coherent `F` and a
  cover all of whose finite intersections are affine (which holds for an affine cover of a scheme
  separated over an affine base, Lemma `lemma-affine-diagonal`, tag 0BDX, line 219), here as
  `R`-modules instead of `Γ(X, 𝒪_X)`-modules, with the ordered Čech complex and the actual right
  derived functor of `R`-module global sections. Stacks deduces 01XD from the Čech-to-cohomology
  spectral sequence; the Lean proof instead compares the sheafified Čech resolution with
  derived functors through the Library's acyclic-resolution comparison.
- `AllPairsCochain`, `allPairsCocycles`, `allPairsD0`, `AllPairsH1`: degree one of the Čech
  complex `Č^•(𝒰, F)` of Cohomology of Sheaves, Definition `definition-cech-complex` (tag 01EF,
  `cohomology.tex` line 913; cochains and differential at lines 880–907): cochains over all `(i₀, i₁) ∈ I²`, and
  `d(s)_{i₀i₁i₂} = s_{i₁i₂} - s_{i₀i₂} + s_{i₀i₁}`, `d(g)_{i₀i₁} = g_{i₁} - g_{i₀}`. The
  cocycle condition is imposed on every open `O` inside the triple intersection, as in the
  Library's `CechDegreeOne.IsCocycle`; by functoriality of restriction it is equivalent to the
  condition on `U_a ∩ U_b ∩ U_c` itself.
- `toAlternating`, `ofAlternating`, `alternatingEquiv`, `allPairsH1EquivHSucc`: degree one of the
  maps `π : Č^• → Č_ord^•` and `c : Č_ord^• → Č^•` (Section `section-alternating-cech`, tag
  01FG, `cohomology.tex` line 4072; ordered cochains at lines 4121–4150, the map `c` at lines
  4166–4187, the map `π` at lines 4211–4222; Definition `definition-ordered-cech-complex`, tag
  01FI, line 4153; Lemmas `lemma-ordered-alternating`, tag 01FJ, line 4194, and
  `lemma-project-to-ordered`, tag 01FK, line 4226) and of Lemma `lemma-alternating-usual` (tag
  01FM, line 4263), which together give `Ȟ¹` of the full and the ordered Čech complexes as the
  same group. The Lean proof does not use the homotopy of 01FM: it shows directly that every
  all-pairs `1`-cocycle is alternating (`allPairs_self`, `allPairs_swap`), so `π` and `c` are
  inverse on cocycles and match the coboundaries.

The alternating complex `F.cochain`, `F.d`, `HSucc` and `ofModules` are the Library's port of the
Anthropic FLT source; `cechCochainComplex` is Stacks' ordered Čech complex (see the Markdown of
`CechResolution.Comparison`). Structure-sheaf quasi-coherence is reused directly from
`CechDegreeOne`. `orderedAffineCoverOfQuasiCompact` is an internal convenience restating the
Library's finite-cover construction for the tangent-to-`H¹` task.
