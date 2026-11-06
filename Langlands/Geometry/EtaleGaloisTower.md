# Finite Galois towers of base changes and smooth Galois actions on étale cohomology

This internal construction builds, for a scheme over a field `K` and a field
extension `L / K`, the tower of base changes to the finite Galois
subextensions of `L / K`. The group `L ≃ₐ[K] L` acts on every level through
restriction. Applying the published canonical deck-tower and level-colimit
constructions, it defines smooth representations of `L ≃ₐ[K] L`, for the
Krull topology, on the colimit over finite Galois subextensions of étale
cohomology with coefficients pulled back from the base. The coefficients are
arbitrary module sheaves on the base, not only constant ones. All
declarations are in namespace `Langlands.Geometry.EtaleGaloisTower`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, considers the action of `Gal(F̄/F)` on
étale cohomology of Shimura varieties with coefficient systems. The published
`EtaleGaloisAction` treats a single base change with constant coefficients.
The coverage note `notes/henniart/harris-cohomology-coverage.md` lists Galois
actions with non-constant coefficients as a missing prerequisite, owned by
Worker 13.

When `L / K` is an algebraic Galois extension, for example a separable
closure, and `X` is quasi-compact and quasi-separated over `K`, étale
cohomology of `X ×_{Spec K} Spec L` is classically the colimit of the
cohomology of the base changes to finite subextensions. Since every finite
subextension lies in a finite Galois one, the finite Galois subextensions are
cofinal, and one may use them. The published statement module
`Langlands.Cohomology.EtaleGaloisSmooth.Statement` records smoothness of the
Galois action for algebraic extensions and quasi-compact quasi-separated
schemes with constant coefficients; its Markdown argues with all finite
subextensions, following SGA 4, Exposé VII, 5.7–5.8. These extra hypotheses
concern that comparison only. Without them the comparison can fail: for
`K = ℚ`, `L = ℚ(2^{1/3})` and `X = Spec L`, the only finite Galois
subextension is `K`, so the degree-zero colimit is `H^0(Spec L, 𝔽₂) = 𝔽₂`,
while `X_L` has two connected components.

This module constructs the colimit over finite Galois subextensions and
proves smoothness of its Galois action. The Lean construction is stated in
the present generality: any field extension `L / K` and any scheme `X` over
`K`. It does not prove that, under the hypotheses above, the colimit is
isomorphic to the étale cohomology of `X ×_{Spec K} Spec L`; that comparison
is a separate theorem obligation. It also makes no finiteness, continuity
beyond smoothness, Shimura-variety or ℓ-adic assertion.

## Inputs

Let `K L : Type u` be fields with `Algebra K L`, let `X : Scheme.{u}`, and let
`f : X ⟶ Spec K`. The inputs are:

- Mathlib's `FiniteGaloisIntermediateField K L`, the lattice of finite Galois
  intermediate fields, with its preorder category;
- `AlgEquiv.restrictNormalHom`, the restriction of automorphisms to a normal
  subextension, and the Krull topology on `L ≃ₐ[K] L`;
- the published base change `EtaleGaloisAction.baseChange K E f`, which is
  `X ×_{Spec K} Spec E`, its maps `specMap` and `baseChangeMap`, and their
  composition and identity laws;
- the published `EtaleCanonicalDeckTower` constructions and the level-colimit
  constructions of `EtaleDeckTowerColimit`.

## The tower

- `levelOver f E` is the base change to `E` as a scheme over `X`, through the
  first projection.
- `levelAut f E σ` is `baseChangeMap f (restrictNormalHom E σ)` as a morphism
  over `X`. `levelAut_mul` and `levelAut_one` follow from the published
  composition law and from multiplicativity of restriction.
  `levelAction f E` is the resulting action of `L ≃ₐ[K] L` on
  `op (levelOver f E)` in `(Over X)ᵒᵖ`. The opposite category reverses
  composition, matching the order of `baseChangeMap_comp`.
- For `h : E ≤ E'`, `specInclusion h : Spec E' ⟶ Spec E` is the spectrum of
  the inclusion. It lies over `Spec K` (`specInclusion_comp_algebraMap`) and
  commutes with the Galois maps (`specInclusion_specMap`), because restriction
  to `E` and to `E'` agree on `E`.
  `specInclusion_refl` and `specInclusion_trans` give functoriality.
- `levelMapScheme f h : X_{E'} ⟶ X_E` is `pullback.map` of the identity of `X`
  and `specInclusion h`, and `levelMap f h` is the same map over `X`.
  `levelMap_levelAut` states Galois equivariance; `levelMap_refl` and
  `levelMap_trans` state functoriality.
- `galoisTower f : FiniteGaloisIntermediateField K L ⥤ Action ((Over X)ᵒᵖ) (L ≃ₐ[K] L)`
  sends `E` to `levelAction f E` and `E ≤ E'` to `levelMap`. The level maps
  point from larger to smaller fields on schemes, so the functor is covariant
  in the opposite category.

## Smoothness

- `levelAut_eq_id_of_mem` states that `levelAut f E σ` is the identity when
  `σ` fixes `E`. Then `restrictNormalHom E σ = 1` by Mathlib's
  `restrictNormal_eq_one_iff`, and the published `baseChangeMap_one`
  applies.
- `isLevelwiseSmooth_galoisTower` states that the tower satisfies the
  published `EtaleCanonicalDeckTower.IsLevelwiseSmooth`. At each level the
  open subgroup is `E.fixingSubgroup`, which is open by Mathlib's
  `IntermediateField.fixingSubgroup_isOpen`.

## Galois representations

The section assumes the published ambient instances
`HasDerivedCategory.{wS}` at every product vertex of the scheme diagram of
`galoisTower f`, and `HasDerivedCategory.{wR} (ModuleCat R)`, for a
commutative ring `R : Type u`. The field `L` is an explicit argument.

- `smoothGaloisCohomologyFunctor L f R q` is the published
  `smoothColimitCohomologyFunctor` for `galoisTower f`. It is a functor from
  module sheaves on `X` to `SmoothRep R (L ≃ₐ[K] L)`. At `M`, it is the colimit
  over `E` of degree `q` étale cohomology of `X_E` with coefficients the
  canonical inverse image of `M`, with `σ` acting through
  `restrictNormalHom E σ`.
- `smoothGaloisSectionsFunctor L f R` is the same construction for global
  sections. `smoothGaloisCohomologyZeroIso` identifies degree zero with
  sections.
- `smoothGaloisLevelCohomologyFunctor L f R q E` is the cohomology of the
  single level `E`, a smooth representation on which `E.fixingSubgroup` acts
  trivially. `smoothGaloisLevelCohomologyι` is its natural map into the
  colimit.
- `galoisCohomology_exists_level` and `galoisSections_exists_level` state that
  every colimit class, respectively section, comes from some finite Galois
  subextension. They specialize the published representative lemmas. The
  required preservation of colimits by the forgetful functor is Mathlib's
  instance for filtered colimits of modules. The index category is filtered
  because it is a nonempty join-semilattice; nonemptiness comes from `⊥`.

## Provenance

This is an internal construction from Mathlib field theory and fiber
products together with the published Galois base change, canonical deck tower
and level-colimit modules. Harris (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, Theorem 5.7 on
printed p. 313, is cited only as motivation. The classical comparison with
the cohomology of `X ×_{Spec K} Spec L` holds only under the additional
hypotheses stated above, as recorded in the published statement module named
there. It is not proved here, and the constructed colimit is not identified
with that cohomology.
