# Adjunction isomorphisms of Hom complexes and of Hom-complex systems

Author: Worker 61. Built on `Langlands.Cohomology.LinearHomComplex`
(`LinearHomComplex.complex`, the Hom complex of two cochain complexes as a
complex of `R`-modules, and `LinearHomComplex.map`, its functoriality by
precomposition and postcomposition), on
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`cochainTransition`,
`cochainTransition_eq_iff`, `ofHom_comp_cochainTransition`,
`homComplexSystem`, `homComplexLimit`, `smoothHomComplexSystem`), on
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`,
`DivisibleSystem.map`, `DivisibleSystem.projection`,
`SmoothRepComplexDivisibleSystem`), on
`Langlands.Cohomology.SupercuspidalExt.Statement` and
`Langlands.Cohomology.SupercuspidalExt.Reciprocity` (namespace
`Langlands.Cohomology.SupercuspidalExt`: `compactInduction`, `restriction`,
`restriction_additive`, `restriction_linear`,
`restriction_preservesHomology`) and on
`Langlands.Representation.Induction.OpenAdjunction`
(`Langlands.Cohomology.SupercuspidalExt.compactInductionAdjunction` and
`Langlands.Induction.smoothCompactInduction_preservesMonomorphisms`). From
Mathlib it uses the Hom-complex API `CochainComplex.HomComplex` (`Cochain.mk`,
`Cochain.ofHom`, `Cochain.map`, `δ_ofHom_comp`, `δ_map`), `Adjunction.homEquiv`
with `homEquiv_unit`, `homEquiv_naturality_left` and
`homEquiv_naturality_right`, `Functor.mapHomologicalComplex`,
`HomologicalComplex.Hom.isoOfComponents`, `NatIso.ofComponents`,
`HasLimit.isoOfNatIso`, `Adjunction.leftAdjoint_preservesColimits`,
`Functor.preservesHomology_of_preservesMonos_and_cokernels`,
`Functor.preservesFiniteLimits_of_preservesHomology` and
`Functor.preservesFiniteColimits_of_preservesHomology`.

## Setting

`R` is a ring, `C` and `D` are `R`-linear preadditive categories with the same
Hom-universe `v`, and `adj : F ⊣ G` is an adjunction between functors
`F : C ⥤ D` and `G : D ⥤ C`, with `G` additive and `R`-linear; from the
cochain part on, `F` is also additive. For cochain complexes `K` in `C` and
`L` in `D`, `F K` and `G L` denote the images under
`F.mapHomologicalComplex` and `G.mapHomologicalComplex`. A cochain of degree
`n` from `K` to `L'` (Mathlib's `Cochain K L' n`) is a family of morphisms
`z.v p q hpq : K ^ p ⟶ L' ^ q` for `p + n = q`; `LinearHomComplex.complex R K L'`
is the complex of `R`-modules of these cochains, with Mathlib's differential
`δ`.

## Hom complexes (namespace `Langlands.Cohomology.LinearHomComplex`)

- `adjunctionHomLinearEquiv R adj X Y : (F X ⟶ Y) ≃ₗ[R] (X ⟶ G Y)`: the
  hom-equivalence `adj.homEquiv X Y` of the adjunction, with additivity and
  `R`-linearity proved from `homEquiv_unit` (the transpose of `f` is
  `adj.unit.app X ≫ G.map f`) and the additivity and `R`-linearity of `G`.
  `adjunctionHomLinearEquiv_apply` and `_symm_apply` state that it and its
  inverse are `adj.homEquiv X Y` and its inverse (by definition).
- `cochainLinearEquiv R adj K L n :
  Cochain (F K) L n ≃ₗ[R] Cochain K (G L) n`: sends a cochain `z` to the
  cochain with components `adj.homEquiv (K ^ p) (L ^ q) (z.v p q hpq)`, and
  conversely by the inverse hom-equivalence. The `simp` lemmas
  `cochainLinearEquiv_v` and `cochainLinearEquiv_symm_v` state these
  component formulas (by definition).
- `unitHom adj K : K ⟶ G (F K)`: the chain map with components
  `adj.unit.app (K ^ p)`; it commutes with the differentials by naturality of
  the unit.
- `cochainLinearEquiv_eq_comp`: the transpose of `z` is the composite
  `Cochain.ofHom (unitHom adj K)` followed by `z.map G` (the cochain with
  components `G.map (z.v p q hpq)`), componentwise by `homEquiv_unit`.
- `δ_cochainLinearEquiv`: the transpose commutes with the differentials,
  `δ n m (cochainLinearEquiv R adj K L n z) =
  cochainLinearEquiv R adj K L m (δ n m z)`. Proof: by the previous lemma and
  Mathlib's `δ_ofHom_comp` and `δ_map`.
- `cochainLinearEquiv_ofHom_comp` and `cochainLinearEquiv_comp_ofHom`: for
  chain maps `f : K' ⟶ K` and `g : L ⟶ L'`, transposing commutes with
  precomposition by `Cochain.ofHom (F f)` and `Cochain.ofHom f`, and with
  postcomposition by `Cochain.ofHom g` and `Cochain.ofHom (G g)`,
  componentwise by `homEquiv_naturality_left` and
  `homEquiv_naturality_right`.
- `adjunctionIso R adj K L :
  LinearHomComplex.complex R (F K) L ≅ LinearHomComplex.complex R K (G L)`:
  the isomorphism of complexes of `R`-modules with components
  `cochainLinearEquiv R adj K L n` (as isomorphisms of modules), commuting
  with the differentials by `δ_cochainLinearEquiv`.
  `adjunctionIso_hom_f_apply` states that its degree `n` component sends `z`
  to `cochainLinearEquiv R adj K L n z` (by definition).
- `map_comp_adjunctionIso_hom`: naturality in both complexes,
  `map R (F f) g ≫ (adjunctionIso R adj K' L').hom =
  (adjunctionIso R adj K L).hom ≫ map R f (G g)` for `f : K' ⟶ K` and
  `g : L ⟶ L'`, from the two previous naturality lemmas.

## Inverse systems of Hom complexes (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `C` and `D` are `R`-linear abelian categories with the same Hom-universe,
`F` and `G` are additive and preserve finite limits and finite colimits, `G`
is `R`-linear, and `T` and `W` are `ℓ`-divisible systems of `ℤ`-graded cochain
complexes in `C` and in `D`. `T.map (F.mapHomologicalComplex _)` is the
`ℓ`-divisible system `m ↦ F (T m)` (the published `DivisibleSystem.map`, which
needs these exactness hypotheses), and similarly `W.map (G.mapHomologicalComplex _)`
is `m ↦ G (W m)`.

- `cochainLinearEquiv_cochainTransition R adj T W h z`: for `m' ≤ m` and a
  cochain `z` from `F (T m)` to `W m`, transposing and then applying the
  transition `cochainTransition` of the Hom-complex system of `T` and
  `G (W ·)` from level `m` to level `m'` gives the transpose of the
  transition of `z` in the Hom-complex system of `F (T ·)` and `W`. Proof:
  by `cochainTransition_eq_iff` it suffices to compare the composites with
  the projections, which follows from `ofHom_comp_cochainTransition` and the
  two naturality lemmas of `cochainLinearEquiv` applied to the projections
  of `T` and `W`.
- `homComplexSystemAdjunctionIso R adj T W :
  homComplexSystem R (T.map (F.mapHomologicalComplex _)) W ≅
  homComplexSystem R T (W.map (G.mapHomologicalComplex _))`: the isomorphism
  of inverse systems `ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ` with level `m`
  component `LinearHomComplex.adjunctionIso R adj (T m) (W m)`, natural by
  the previous lemma. `homComplexSystemAdjunctionIso_hom_app` states the
  components (by definition).
- `homComplexLimitAdjunctionIso R adj T W`: the induced isomorphism
  `homComplexLimit R (T.map (F.mapHomologicalComplex _)) W ≅
  homComplexLimit R T (W.map (G.mapHomologicalComplex _))` of Mathlib's
  chosen limit objects (`HasLimit.isoOfNatIso`).
  `homComplexLimitAdjunctionIso_hom_π` (`simp`, with a `reassoc` form) states
  that it commutes with the limit projections to level `m` and
  `LinearHomComplex.adjunctionIso R adj (T m) (W m)`.

## Compact induction and restriction (namespace `Langlands.Cohomology`)

`R : Type u` is a commutative ring, `G : Type u` a topological group, `H` a
subgroup of `G` and `hH : IsOpen (H : Set G)`. `compactInduction R G H` and
`restriction R G H` are the published one-universe functors between smooth
representations of `H` and of `G` (compact induction `c-Ind_H^G`: functions
`f : G → V` with `f (h x) = h · f x` for `h ∈ H`, invariant under right
translation by some open subgroup and with compact support modulo `H`, with
`G` acting by right translation; and restriction of the action to `H`).

- `compactInduction_additive` (instance, no openness hypothesis): compact
  induction is additive. The map of `compactInduction R G H` on a morphism
  acts by composition on values, so it sends a sum of morphisms to the sum of
  the maps (checked on elements, by definition).
- `compactInduction_preservesHomology R hH`: for open `H`, compact induction
  is exact. Proof: it preserves monomorphisms
  (`Induction.smoothCompactInduction_preservesMonomorphisms`) and, as the left
  adjoint of `compactInductionAdjunction R G H hH`, it preserves colimits,
  hence cokernels; Mathlib's
  `Functor.preservesHomology_of_preservesMonos_and_cokernels` concludes.
- `compactInductionSystem R hH T`: for an `ℓ`-divisible system `T` of cochain
  complexes of smooth representations of `H`
  (`SmoothRepComplexDivisibleSystem.{u, u, u} R H ℓ`), the `ℓ`-divisible
  system `m ↦ c-Ind_H^G (T m)` of cochain complexes of smooth
  representations of `G`, i.e. `T.map` of the levelwise compact induction
  functor on complexes, with the finite limit and colimit preservation
  obtained from exactness.
- `restrictionSystem R hH W`: for an `ℓ`-divisible system `W` of cochain
  complexes of smooth representations of `G`, the `ℓ`-divisible system
  `m ↦ W m|_H`, in the same way from `restriction_preservesHomology`.
- `smoothHomComplexSystemReciprocityIso R hH T W :
  smoothHomComplexSystem R G (compactInductionSystem R hH T) W ≅
  smoothHomComplexSystem R H T (restrictionSystem R hH W)`: the instance of
  `homComplexSystemAdjunctionIso` for the adjunction
  `compactInductionAdjunction R G H hH : compactInduction R G H ⊣
  restriction R G H` (restriction is additive and `R`-linear by the published
  instances). At level `m` and in degree `n`, it sends a family of
  `G`-equivariant maps `c-Ind_H^G (T m ^ p) ⟶ W m ^ q` to the family of the
  corresponding `H`-equivariant maps `T m ^ p ⟶ W m ^ q` under Frobenius
  reciprocity for compact induction from the open subgroup `H`.
- `smoothHomComplexLimitReciprocityIso R hH T W`: the induced isomorphism of
  the limits `homComplexLimit` of the two inverse systems
  (`HasLimit.isoOfNatIso`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.311
(one-based PDF page 13). Harris writes: "We need to check that the complexes
used to obtain the spectral sequences (4.9) satisfy a Mittag-Leffler
condition as m varies. By (4.4.4) and (4.8), these are of the form
`⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ) ∈ O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ),
Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`, which can be rewritten (4.10.2)
`⊕_{i+j=k} ⊕_{(e,δ) ∈ O_{-i}} Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ),
Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`."

The rewriting replaces Hom out of a compact induction `c-Ind_{S(ẽ)}^{GJ}` by
Hom out of the inducing `S(ẽ)`-module, which is Frobenius reciprocity for
compact induction from the open subgroup `S(ẽ)`; Harris does not spell this
out. This module formalizes that step for Hom complexes and for the inverse
systems over `m` of Hom complexes of `ℓ`-divisible systems formed in the
published HomSystem module, which reads Harris's maps (4.10.3) as
`homTransition`. The general adjunction statements and the proofs are ours;
Frobenius reciprocity itself is the published
`compactInductionAdjunction`, and the additivity and exactness of compact
induction are proved here because the Library did not provide them.

## Scope

The module does not identify Harris's complexes (4.10.2), the modules
`C^j_m(ẽ)` or the coefficients `Hom(𝒪_m[K_p/H_p]^M, 𝓛_m)` with Hom complexes
of `ℓ`-divisible systems. It does not treat the splitting of Hom out of the
direct sum over `(e, δ) ∈ O_{-i}` into a sum of Hom modules, the passage from
`K_p/H_p` to `C_p/H_p` in the coefficients, the total complex over
`i + j = k`, or Harris's Mittag-Leffler argument. It does not compare the
isomorphisms with the inclusions of the `ℓ`-divisible systems or with
cohomology, Ext groups or the spectral sequences.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
