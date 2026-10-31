# Hom into reductions: Harris's system Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.FreeReduction`
(`freeOverPowQuotient_cokernel_powSMul_of_free`),
`Langlands.Cohomology.DivisibleSystem.LeftExact`
(`DivisibleSystem.mapLeftExact`) and
`Langlands.Representation.Induction.PermutationDual`
(`Induction.linHom_permutation_asModule_free`). Through their imports it uses
`powSMul`, `map_powSMul`, `DivisibleSystem`, `DivisibleSystem.epi_projection`
and `DivisibleSystem.hom_ext` (`Langlands.Cohomology.DivisibleSystem`),
`powSMul_hom_apply` and `FreeOverPowQuotient`
(`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`),
`freeOverPowQuotient_of_iso`
(`Langlands.Cohomology.DivisibleSystem.FreeRestrictScalars`), `reductionTower`,
`reductionπ`, `reductionπIsCokernel`, `powSMul_comp_reductionπ`,
`reductionπ_map`, `reductionInclusion`, `reductionπ_inclusion`,
`reductionSystem` and `mono_powSMul_one_iff_isSMulRegular`
(`Langlands.Cohomology.DivisibleSystem.Reduction`), and
`Induction.permutation`
(`Langlands.Representation.Induction.PermutationModule`). From Mathlib it uses
the internal Hom of representations `Rep.ihom` with the adjunction
`ihom.adjunction` (`A ⊗ - ⊣ Rep.ihom A`), `Adjunction.rightAdjoint_preservesLimits`,
`PreservesLimits.preservesFiniteLimits`, `Module.projective_lifting_property`,
`LinearMap.rangeRestrict`, `LinearMap.codRestrict`, `Rep.epi_iff_surjective`,
`ShortComplex.exact_of_g_is_cokernel`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.moduleCat_exact_iff`,
`ShortComplex.Exact.gIsCokernel`, `IsColimit.coconePointUniqueUpToIso`,
`NatIso.ofComponents`, `Representation.trivial`, `MulAction.stabilizer` and
`IsCancelSMul.stabilizer_eq_bot`.

## Conventions

`ℓ` and `m` are natural numbers, `R` is a commutative ring and `G` a group.
For representations `A` and `L` in `Rep R G`, `Hom_R(A, L)` denotes Mathlib's
`(Rep.ihom A).obj L`: the `R`-linear maps `A → L`, on which `g : G` acts by
`φ ↦ L.ρ g ∘ φ ∘ A.ρ g⁻¹`; on morphisms, `Rep.ihom A` is composition. In
Mathlib, for `A` in `Rep.{w} R G`, `Rep.ihom A` is a functor from `Rep.{w'} R G`
to `Rep.{max w w'} R G`; every use below except the additivity instance
fixes `w' = w`. "`A` is projective over `R`" means `Module.Projective R A`
for the underlying `R`-module (instance argument).

`powSMul ℓ m X` is the published endomorphism "multiplication by `ℓ ^ m`" of
an object `X`; for a representation its underlying map is `x ↦ ℓ ^ m • x`
(`powSMul_hom_apply`). The published `reductionTower ℓ L` is the inverse
system whose level `m` is `cokernel (powSMul ℓ m L)`, written `L / ℓ ^ m L`,
with projections `reductionπ ℓ L m : L ⟶ L / ℓ ^ m L`; the published
`reductionInclusion ℓ L h : L / ℓ ^ m' L ⟶ L / ℓ ^ m L` for `h : m' < m` is
induced by multiplication by `ℓ ^ (m - m')`. When multiplication by `ℓ` is a
monomorphism on `L` (instance argument `[Mono (powSMul ℓ 1 L)]`), the
published `reductionSystem ℓ L` is the `ℓ`-divisible system with tower
`reductionTower ℓ L` and inclusions `reductionInclusion`. The published
predicate `FreeOverPowQuotient ℓ m P` states that `P` is killed by `ℓ ^ m`
and is free over `(R ⧸ (ℓ ^ m))[G]`, where `(ℓ ^ m)` is the ideal
`Ideal.span {((ℓ : R) ^ m)}` and `k[G]` is `MonoidAlgebra k G`; "`P` is free
over `R[G]`" means `Module.Free (MonoidAlgebra R G) P.ρ.asModule`.

## Hom_R(A, -) and reduction modulo ℓ ^ m (namespace `Langlands.Cohomology.DivisibleSystem`)

`R : Type u`, `G : Type v`, and `A`, `L` are in `Rep.{w} R G`.

- `ihom_map_hom_apply`: `(Rep.ihom A).map f` sends `φ` to `a ↦ f (φ a)`
  (by definition).
- `ihom_additive`: `Rep.ihom A` is an additive functor; sums of morphisms go
  to sums of compositions, checked pointwise.
- `mono_powSMul_ihom`: if multiplication by `ℓ` is a monomorphism on `L`, it is
  one on `Hom_R(A, L)`. Through `mono_powSMul_one_iff_isSMulRegular` both
  statements mean that `(ℓ : R)` is a non-zero-divisor on the module, and
  `ℓ • φ = ℓ • ψ` gives `ℓ • φ a = ℓ • ψ a` for every `a`.
- `powSMul_comp_ihom_map_reductionπ`: multiplication by `ℓ ^ m` on
  `Hom_R(A, L)` followed by composition with `reductionπ ℓ L m` is zero; by
  additivity (`map_powSMul`) it is the image under `Rep.ihom A` of
  `powSMul ℓ m L ≫ reductionπ ℓ L m = 0` (`powSMul_comp_reductionπ`).
  `ihomReductionComplex ℓ A L m` is the short complex in `Rep R G` formed by
  these two maps.

From here on `A` is projective over `R`.

- `ihom_map_surjective`, `epi_ihom_map`: for an epimorphism `p : X ⟶ Y`,
  composition with `p` is surjective on `Hom_R(A, -)`, since every `R`-linear
  `ψ : A → Y` lifts along the surjection `p` (`Module.projective_lifting_property`,
  `Rep.epi_iff_surjective`); hence `(Rep.ihom A).map p` is an epimorphism.
- `exists_pow_smul_of_ihom_map_reductionπ_eq_zero`: if `φ : A → L` composed
  with `reductionπ ℓ L m` is zero, then `φ = ℓ ^ m • ψ` for some `ψ : A → L`.
  The sequence `L → L → L / ℓ ^ m L` (multiplication by `ℓ ^ m`, then
  `reductionπ`) is exact (`ShortComplex.exact_of_g_is_cokernel`), also after
  the faithful forgetful functor to `ModuleCat R`
  (`ShortComplex.exact_map_iff_of_faithful`), where it means that every
  element killed by `reductionπ` is `ℓ ^ m` times an element
  (`ShortComplex.moduleCat_exact_iff`). So `φ` lands in the image of
  multiplication by `ℓ ^ m`, and `ψ` is a lift of `φ`, viewed as a map into
  that image (`LinearMap.codRestrict`), along the surjection onto the image
  (`LinearMap.rangeRestrict`), by projectivity of `A`.
- `ihomReductionComplex_exact`: `ihomReductionComplex ℓ A L m` is exact.
  After the forgetful functor to `ModuleCat R`, this is the previous lemma.
- `ihomReductionIso ℓ A L m : Hom_R(A, L) / ℓ ^ m ≅ Hom_R(A, L / ℓ ^ m L)`
  (`(reductionTower ℓ ((Rep.ihom A).obj L)).obj (op m)` and
  `(Rep.ihom A).obj ((reductionTower ℓ L).obj (op m))`). The second map of the
  exact complex `ihomReductionComplex ℓ A L m` is an epimorphism
  (`epi_ihom_map`), hence a cokernel of the first
  (`ShortComplex.Exact.gIsCokernel`); the isomorphism is the comparison of this
  cokernel with `reductionπIsCokernel` (`IsColimit.coconePointUniqueUpToIso`).
  `reductionπ_ihomReductionIso_hom`: the projection onto `Hom_R(A, L) / ℓ ^ m`
  followed by the isomorphism is composition with `reductionπ ℓ L m`.
- `ihomReductionIso_naturality`: the isomorphisms commute with the
  projections `· / ℓ ^ m ⟶ · / ℓ ^ n` (`n ≤ m`) of both towers.
  `ihomReductionIso_inclusion`: they commute with the maps
  `reductionInclusion` of both towers (on the target side, with
  `(Rep.ihom A).map (reductionInclusion ℓ L h)`). Both are checked after the
  epimorphism `reductionπ` onto the source, using
  `reductionπ_ihomReductionIso_hom`, `reductionπ_map`,
  `reductionπ_inclusion` and `map_powSMul`.
- `ihomReductionTowerIso ℓ A L : reductionTower ℓ ((Rep.ihom A).obj L) ≅ reductionTower ℓ L ⋙ Rep.ihom A`
  assembles the `ihomReductionIso ℓ A L m` (`NatIso.ofComponents`, naturality
  by `ihomReductionIso_naturality`); `ihomReductionTowerIso_hom_app` states
  that its component at `m` is `ihomReductionIso ℓ A L m`.

## The ℓ-divisible system m ↦ Hom_R(A, L / ℓ ^ m L)

`R : Type u`, `G : Type v`, and `A`, `L` are in `Rep.{u} R G`: Mathlib's
monoidal closed structure on representations, which provides
`ihom.adjunction`, requires the carriers to be in the universe of `R`.

- `ihom_preservesFiniteLimits`: `Rep.ihom A` preserves finite limits, being a
  right adjoint (`Adjunction.rightAdjoint_preservesLimits`; preservation of
  finite limits follows by instance search,
  `PreservesLimits.preservesFiniteLimits`).

From here on `A` is projective over `R` and multiplication by `ℓ` is a
monomorphism on `L`.

- `ihomReductionSystem ℓ A L` (the entry declaration) is the image of
  `reductionSystem ℓ L` under `Rep.ihom A`, built with the published
  `DivisibleSystem.mapLeftExact`. Its hypotheses are that the functor is
  additive and preserves finite limits (the two instances above), and that
  the images of the projections `j` of `reductionSystem ℓ L` are epimorphisms:
  these projections are epimorphisms (`DivisibleSystem.epi_projection`) and
  `Rep.ihom A` preserves epimorphisms (`epi_ihom_map`).
  `ihomReductionSystem_obj`: its level `m` is `Hom_R(A, L / ℓ ^ m L)`
  (by definition).
- `reductionSystemIhomIso ℓ A L : reductionSystem ℓ ((Rep.ihom A).obj L) ≅ ihomReductionSystem ℓ A L`:
  the components of `ihomReductionTowerIso` and of its inverse are morphisms
  of `ℓ`-divisible systems, since they commute with the inclusions `i`
  (`ihomReductionIso_inclusion`); the two composites are identities because
  the underlying morphisms of towers are (`DivisibleSystem.hom_ext`).
  The instance `mono_powSMul_ihom` makes the left-hand side defined.

## Freeness of the levels

`R`, `G : Type u`, and `A`, `L` are in `Rep.{u} R G` with `A` projective over
`R`.

- `freeOverPowQuotient_ihom_reduction A L m`: if `Hom_R(A, L)` is free over
  `R[G]` (instance argument), then `Hom_R(A, L / ℓ ^ m L)` satisfies
  `FreeOverPowQuotient ℓ m`. The cokernel of multiplication by `ℓ ^ m` on
  `Hom_R(A, L)` does (`freeOverPowQuotient_cokernel_powSMul_of_free`), and the
  predicate transfers along `ihomReductionIso ℓ A L m`
  (`freeOverPowQuotient_of_iso`).
- `freeOverPowQuotient_ihomReductionSystem_obj A L m`: the same for level `m`
  of `ihomReductionSystem ℓ A L`, when multiplication by `ℓ` is a
  monomorphism on `L`.

## Harris's permutation modules

`R : Type u`; `M` and `L` are `R`-modules in `Type u`, `M` finite free and `L`
free. `Representation.trivial R G L` is `L` with the trivial action of `G`,
and `Induction.permutation R G X M` is the published permutation
representation on `M[X] = X →₀ M` for a `G`-set `X`, with `G` permuting the
points of `X`.

- `freeOverPowQuotient_permutation_ihom_reduction h m`: if `G : Type u` acts on
  a finite `X : Type u` with trivial stabilizers (`h`), then
  `Hom_R(M[X], L / ℓ ^ m L)`, for the permutation representation `M[X]` and
  `L` with the trivial action, satisfies `FreeOverPowQuotient ℓ m`.
  `Hom_R(M[X], L)` is free over `R[G]`
  (`Induction.linHom_permutation_asModule_free`), and `M[X]` is projective
  over `R` (free, as `M` is), so `freeOverPowQuotient_ihom_reduction` applies.
- `freeOverPowQuotient_subgroup_permutation_ihom_reduction S m`: for a
  subgroup `S` of a finite group `Q : Type u`, acting on `Q` by left
  multiplication, `Hom_R(M[Q], L / ℓ ^ m L)` satisfies `FreeOverPowQuotient ℓ m`
  as a representation of `S`; left multiplication has trivial stabilizers
  (`IsCancelSMul.stabilizer_eq_bot`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- proof of Proposition 4.10, printed p.312 (one-based PDF page 14): "Since
  `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
  `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are
  surjective for all `m`."
- §4, printed p.311 (one-based PDF page 13): "let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any
  `m`. Then `𝓛_m` forms an inverse system of `𝒪`-modules".

This module formalizes the second freeness claim, for the Lean module
`Hom_R(M[X], L / ℓ ^ m L)`, where `R` plays the role of `𝒪`, `L` of the
lattice `𝓛`, `L / ℓ ^ m L` of `𝓛_m` (through the published
`reductionSystem`), `M[X]` of `𝒪[C_p/H_p]^M` with `M = 𝒪^M`, and `G` of
`S(ẽ)/H_p` acting freely on `X = C_p/H_p`; in Harris's case `Q = C_p/H_p`
and `S = S(ẽ)/H_p` when `H_p` is normal in `C_p`. That `S(ẽ)/H_p` acts
trivially on `𝓛` and freely on `C_p/H_p` is our reading of Harris's setting,
as in the published PermutationDual module. It also shows that the modules
`Hom_R(A, L / ℓ ^ m L)` form an `ℓ`-divisible system isomorphic to the
reduction system of `Hom_R(A, L)`, so that the published Hom-system results
for reduction systems of free representations (FreeReduction) apply to it.
Harris asserts the freeness in the quoted sentence without further argument
and does not state that `Hom_R(A, -)` commutes with reduction modulo `ℓ ^ m`
for projective `A`, a standard fact. The formulation and all proofs are
ours. The module is derived.

## Scope

The Lean module is `Hom_R(M[X], L / ℓ ^ m L)`, the `R`-linear maps from
`M[X]` into the reduction. Harris's `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` consists of
`𝒪_m`-linear maps out of `𝒪_m[C_p/H_p]^M`. Mathematically both are the
maps out of `M[X] / ℓ ^ m M[X]` into a module killed by `ℓ ^ m`, but this
identification is not formalized, nor is the identification of `𝓛 ⊗_𝒪 𝒪_m` with `𝓛 / ℓ^m 𝓛`.
The module does not identify `C^j_m(ẽ)^{H_p}` with a reduction, and it does
not formalize Harris's identifications (4.7) and (4.8) of automorphic forms
with these modules. The results of the last two sections require `G` and
the carriers in the universe of `R`. Everything concerns the categories
`Rep` of representations of abstract groups, not categories of smooth
representations.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
