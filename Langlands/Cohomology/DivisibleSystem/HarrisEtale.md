# Harris's étale coefficient sheaves as `ℓ`-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem` with `tower`,
`inclusion`, `projection`, `powSMul`, `comp_powSMul`,
`powSMul_comp_powSMul`, `map_powSMul`, `shortComplex_exact_congr`, `Hom`,
`hom_ext`, `id_tower`, `comp_tower` and `map`),
`Langlands.Cohomology.DivisibleSystem.LeftExact` (`mapLeftExact`),
`Langlands.Cohomology.DivisibleSystem.ReductionLattice`
(`harrisReductionSystem`, `harrisReductionSystemTowerIso`), Worker 13's
`Langlands.Shimura.Coefficients.HarrisEtaleCoefficients`
(`harrisEtaleCoefficientSystem`, `harrisEtaleSectionsSystem`) and
`Langlands.Shimura.Coefficients.EtaleExact`
(`etaleAssociatedFunctorPreservesFiniteLimits`,
`etaleAssociatedFunctorPreservesFiniteColimits`). Through their imports it
uses Worker 13's `EquivariantDiagram` with `action` and `transition`
(`Langlands.CategoryTheory.EquivariantDiagram`),
`etaleAssociatedVaryingSystem`, `etaleAssociatedComparisonIso` and
`etaleAssociatedReduction`
(`Langlands.Shimura.Coefficients.VaryingCoverInverse`) and
`EtaleDerivedSections.sections` (`Langlands.Geometry.EtaleDerivedSections`,
with its additivity and finite-limit instances); Worker 57's
`IsFiniteGeometricTorsor` and `etaleAssociatedFunctor`
(`Langlands.Shimura.Coefficients.Etale`), `harrisCongruenceGroups` and
`harrisCoefficientDiagram`
(`Langlands.Shimura.Coefficients.HarrisCongruenceLevels`),
`torsionCongruenceGroups` and `congruenceKernel`
(`Langlands.Shimura.Coefficients.FiniteQuotient`), `torsionSystem`
(`Langlands.Shimura.Coefficients.Lattice`), `HarrisCoefficientIntegers` and
`harrisLatticeAction` (`Langlands.Shimura.Coefficients.HarrisLattice`); and
`harrisCoefficientScalarIdeal`
(`Langlands.Shimura.Coefficients.HarrisReduction`). From Mathlib it uses
`Action`, `Action.forget` (faithful, preserving finite limits and colimits),
`Action.res`, `Action.Hom.ext`, `ShortComplex.isoMk`,
`ShortComplex.exact_of_iso`, `ShortComplex.shortExact_of_iso`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.Exact.map`,
`ShortComplex.ShortExact.map_of_exact`, `Functor.mono_of_mono_map`,
`Functor.epi_of_epi_map`, `Iso.inv_hom_id_app_assoc`,
`QuotientGroup.induction_on`, `Scheme.smallEtaleTopology` and the abelian
category of sheaves of modules on it.

## Conventions

`ℓ` and `m` are natural numbers. An `ℓ`-divisible system `T` in an abelian
category (published `DivisibleSystem`, Harris (2.1)) is an inverse system
`T.tower : ℕᵒᵖ ⥤ C`, with objects `T m` and maps `j : T m ⟶ T m'` for
`m' ≤ m` (`T.projection`), and maps `i : T m' ⟶ T m` for `m' < m`
(`T.inclusion`), such that `ℓ ^ m` is zero on `T m`, the sequence
`0 ⟶ T m' ⟶ T m ⟶ T (m - m') ⟶ 0` of `i` and `j` is short exact, `i` is a
kernel of `ℓ ^ m'` on `T m` (`torsion_exact`), and
`T (a + b) ⟶ T (a + b) ⟶ T (a + b)` given by `ℓ ^ a` and `ℓ ^ b` is exact
(`flat`). `powSMul ℓ m X` is multiplication by `ℓ ^ m` on `X`. As in the
published module the index starts at `0`, and `T 0` is zero.

For a group `G` and a category `V`, `Action V G` is Mathlib's category of
objects of `V` with an action of `G`; for a group homomorphism `φ`,
`Action.res V φ` restricts actions along `φ`. For an inverse system of groups
`D : ℕᵒᵖ ⥤ GrpCat`, Worker 13's `EquivariantDiagram D C` is an inverse
system `obj : ℕᵒᵖ ⥤ C` with actions `ρ n` of `D n` on `obj n` for which the
maps of `obj` are equivariant along the maps of `D`; `action n` is the object
`obj n` of `Action C (D n)`, and `transition f : action i ⟶ res (action j)` is
the map `obj.map f` as a morphism of representations of `D i`, which acts on
`obj j` through `D.map f`.

For a scheme `X`, a commutative ring `R` and a group `G`,
`etaleAssociatedFunctor X Y : Action (ModuleCat R) G ⥤ Sheaf` sends a
representation `M` of `G` to the sheaf on the small étale site of `X` of
invariants of the diagonal action of `G` on sections of the constant sheaf
`M` over a `G`-object `Y` of the small étale site. We write `Assoc_Y`. When
`Y` is a finite geometric torsor over `X` (`IsFiniteGeometricTorsor`: `G`
finite, `Y ⟶ X` finite and surjective, `G` simply transitive on geometric
fibres), `Assoc_Y` preserves finite limits and finite colimits (published
`EtaleExact`), so it is exact and carries (short) exact sequences to (short)
exact sequences.

For `Y : EquivariantDiagram D X.Etale` with finite geometric torsors `Y n`
(hypothesis `hY`) and a coefficient diagram
`M : EquivariantDiagram D (ModuleCat R)`, the published
`etaleAssociatedVaryingSystem X Y hY M : ℕᵒᵖ ⥤ Sheaf` has objects
`Assoc_{Y n} (M n)`. For `f : op m ⟶ op m'` (`m' ≤ m`) its map is
`τ_f = β_f ≫ α_f⁻¹`, where `β_f = Assoc_{Y m}(M.transition f)` maps to
`B_f = Assoc_{Y m}(res M m')` (`etaleAssociatedReduction`) and
`α_f : Assoc_{Y m'}(M m') ≅ B_f` is the proved comparison along the cover map
`Y m ⟶ Y m'` (`etaleAssociatedComparisonIso`, a natural isomorphism in `M`).

## Transport along an isomorphism of inverse systems

`C` is an abelian category and `T` an `ℓ`-divisible system in `C`.

- `ofTowerIso T e`: for an isomorphism `e : T.tower ≅ F` of inverse systems,
  the `ℓ`-divisible system with tower `F` and maps
  `i = e⁻¹ ≫ T.inclusion ≫ e`. The axioms are transported: `ℓ ^ m` commutes
  with `e`, and the three sequences are isomorphic to those of `T` through
  the components of `e` (`ShortComplex.isoMk`). `ofTowerIso_inclusion`
  records the maps `i`.
- `isoOfTowerIso T e : T ≅ T.ofTowerIso e`, with tower components `e.hom` and
  `e.inv`.

## Exactness for actions

`V` is an abelian category and `G` a group. The forgetful functor
`Action.forget V G` is faithful and preserves finite limits and colimits.

- `powSMul_action_hom ℓ m N`: multiplication by `ℓ ^ m` on an action `N` has
  underlying morphism multiplication by `ℓ ^ m` on the underlying object
  (`map_powSMul`).
- `action_exact_of_map S h`: a short complex `S` of actions is exact when its
  underlying short complex is (`exact_map_iff_of_faithful`, since the
  forgetful functor is faithful and preserves homology).
- `action_shortExact_of_map S h`: likewise for short exactness, a faithful
  functor reflecting monomorphisms and epimorphisms.

## Equivariant structures

`T` is an `ℓ`-divisible system in `C` and `D : ℕᵒᵖ ⥤ GrpCat` an inverse
system of groups. A structure `A : T.EquivariantStructure D` consists of
actions `act n` of `D n` on `T n` such that the maps `j` are equivariant
along the maps of `D` (`comm`) and every map `i : T m' ⟶ T m` is equivariant
for `D m`, which acts on `T m'` through `D m ⟶ D m'` (`inclusion_comm`).

- `A.diagram`: `T.tower` with these actions, as an `EquivariantDiagram D C`.
- `A.inclusionHom h`: the map `i : T m' ⟶ T m` as a morphism of
  representations of `D m` from `res (T m')` to `T m`;
  `inclusionHom_hom` records the underlying map.
- `A.powSMul_eq_zero m`: `ℓ ^ m` is zero on the representation `T m`.
- `A.shortComplex h`: the sequence `res (T m') ⟶ T m ⟶ res (T (m - m'))` of
  representations of `D m`, of `inclusionHom` and
  `A.diagram.transition`; `shortComplex_shortExact`: it is short exact.
- `A.torsionShortComplex h`: the sequence `res (T m') ⟶ T m ⟶ T m` of
  `inclusionHom` and `ℓ ^ m'`; `torsionShortComplex_exact`: it is exact.
- `A.flatShortComplex a b`: the sequence of `ℓ ^ a` and `ℓ ^ b` on the
  representation `T (a + b)`; `flatShortComplex_exact`: it is exact.

Each exactness statement is the corresponding axiom of `T`, by the lemmas on
actions.

## Associated étale sheaves

`X : Scheme.{u}`, `R : Type u` is a commutative ring, `D : ℕᵒᵖ ⥤ GrpCat.{u}`,
`Y : EquivariantDiagram D X.Etale` with `hY : ∀ n, IsFiniteGeometricTorsor X
(Y.action n)`, and `A` is an equivariant structure on an `ℓ`-divisible system
`T` of `R`-modules. Write `𝓛 m = Assoc_{Y m}(T m)`, the objects of
`etaleAssociatedVaryingSystem X Y hY A.diagram`, whose maps are the maps `j`
of the sheaves.

- `A.etaleInclusion X Y hY h : 𝓛 m' ⟶ 𝓛 m`, for `m' < m`: the comparison
  `α_f : 𝓛 m' ≅ Assoc_{Y m}(res (T m'))` for `f : op m ⟶ op m'`, followed by
  `Assoc_{Y m}` of the equivariant map `inclusionHom h`.
- `etale_powSMul_eq_zero`: `ℓ ^ m` is zero on `𝓛 m`, since the additive
  functor `Assoc_{Y m}` commutes with `ℓ ^ m`.
- `etaleInclusion_comp`: `i ≫ j = 0` on `𝓛 m' ⟶ 𝓛 m ⟶ 𝓛 (m - m')`: by
  definition of `τ`, the composite is
  `α ≫ Assoc_{Y m}(inclusionHom ≫ transition) ≫ α⁻¹`, and the middle
  composite is zero.
- `etale_shortExact`: the sequence `0 ⟶ 𝓛 m' ⟶ 𝓛 m ⟶ 𝓛 (m - m') ⟶ 0` is
  short exact. `Assoc_{Y m}` is exact by `hY m`, so the image of
  `A.shortComplex h` is short exact, and it is isomorphic to the étale
  sequence by the comparisons `α⁻¹` at the two ends and the identity in the
  middle; the squares commute by the definitions of `etaleInclusion` and of
  `τ = β ≫ α⁻¹`.
- `etale_torsion_exact`: `𝓛 m' ⟶ 𝓛 m ⟶ 𝓛 m`, of `i` and `ℓ ^ m'`, is exact:
  the image of `A.torsionShortComplex h`, with `α⁻¹` at the left end and
  identities elsewhere.
- `etale_flat`: the sequence of `ℓ ^ a` and `ℓ ^ b` on `𝓛 (a + b)` is exact,
  the image of `A.flatShortComplex a b`.
- `A.etaleSystem X Y hY`: the `ℓ`-divisible system in the category of
  sheaves of `R`-modules on the small étale site of `X` with tower
  `etaleAssociatedVaryingSystem X Y hY A.diagram` and maps `i` the maps
  `etaleInclusion` (`etaleSystem_tower`, `etaleSystem_inclusion`).

## Harris's coefficient sheaves

`ℓ` is a nonzero natural number (`[NeZero ℓ]`). As in the published
`HarrisEtaleCoefficients`, `A` is a finite-dimensional `ℚ`-algebra with
Worker 13's involution `σ`, `L` a number field, `W` a finite-dimensional
`L`-module with an algebraic representation `ρ` of `σ.baseChange L`, `p` a
finite place of `ℚ` and `U` a compact open level of `σ.FiniteAdelicPoints`.
`R = HarrisCoefficientIntegers L p` is the product of the completed integer
rings of `L` at the places above `p`, and `𝓛` is Worker 57's stable lattice
with the action `harrisLatticeAction ρ p U` of `U.subgroup`. The published
`harrisCoefficientScalarIdeal L p ℓ` is the ideal `(ℓ)` of `R`, so the
published `harrisCoefficientDiagram ρ p U ℓ` has the modules `𝓛 / ℓ ^ m 𝓛`
(Worker 57's `torsionSystem`), with actions of the groups
`harrisCongruenceGroups ρ p U ℓ`: at `m`, the quotient of `U.subgroup` by the
kernel `congruenceKernel` of its action on `𝓛 / ℓ ^ m 𝓛`.

- `harrisTorsionDivisibleSystem ℓ ρ p U`: the `ℓ`-divisible system of
  `R`-modules `𝓛 / ℓ ^ m 𝓛`: the published `harrisReductionSystem` (the
  cokernels of `ℓ ^ m` on `𝓛`, as representations of `U.subgroup`),
  transported by `ofTowerIso` along the published
  `harrisReductionSystemTowerIso` to `torsionSystem`, and sent to modules by
  the published `DivisibleSystem.map` for `Action.forget`.
  `harrisTorsionDivisibleSystem_tower`: its tower is, by definition, the
  underlying inverse system of `harrisCoefficientDiagram ρ p U ℓ`.
- `harrisEquivariantStructure ℓ ρ p U`: the actions and equivariance of
  `harrisCoefficientDiagram` form an equivariant structure for
  `harrisCongruenceGroups ρ p U ℓ`. For `inclusion_comm`, the class of
  `g ∈ U` acts on `𝓛 / ℓ ^ m 𝓛` as `g` does (`QuotientGroup.induction_on`),
  and the transported maps `i` are morphisms of representations of `U`.
  `harrisEquivariantStructure_diagram`: its diagram is
  `harrisCoefficientDiagram ρ p U ℓ`.

Let `X : Scheme.{u}`, `Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ)
X.Etale` and `hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n)`.

- `harrisEtaleDivisibleSystem ℓ ρ p U X Y hY` (the entry declaration):
  the `ℓ`-divisible system `etaleSystem` of `harrisEquivariantStructure`.
  `harrisEtaleDivisibleSystem_tower`: its tower is, by definition, the
  published `harrisEtaleCoefficientSystem ρ p U ℓ X Y hY`.
- `harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ`: the global
  sections. Global sections (`EtaleDerivedSections.sections X R`) are
  additive and left exact but not right exact, so the hypothesis `hΓ`
  requires that the sections of every map `j` of
  `harrisEtaleDivisibleSystem` be epimorphisms, that is, surjective; the
  system is the published `mapLeftExact`.
  `harrisEtaleSectionsDivisibleSystem_tower`: its tower is, by definition,
  the published `harrisEtaleSectionsSystem ρ p U ℓ X Y hY`. By the published
  `epi_map_projection_of_succ`, `hΓ` follows from the case of the maps
  `j : 𝓛 (m + 1) ⟶ 𝓛 m`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- §2, printed p.304 (one-based PDF page 6), the definition of `ℓ`-divisible
  systems, quoted and interpreted in the published `DivisibleSystem` module:
  maps `i : T_{m'} → T_m` and `j : T_m → T_{m−m'}` with
  "(2.1) `0 → T_{m'} → T_m → T_{m−m'} → 0` is exact".
- §4, printed p.311 (one-based PDF page 13): "The constant étale sheaf `𝓛̃_m`
  on `S(GG, X_{n−1})_{K(N,m)}` descends to a lisse étale sheaf, still denoted
  `𝓛̃_m`, on `S(GG, X_{n−1})_{K(N)}`", and "Now we want to let `m` vary. Let
  the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
  `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of
  `𝒪`-modules, and the inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf
  `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_{K(N)}`."

Harris states only that `{𝓛̃_m}` is an inverse system; he does not state
that it is an `ℓ`-divisible system in the sense of (2.1), and he does not
construct maps `i` for it. The maps `i`, the equivariant structures and all
statements and proofs here are ours; the module is derived. The construction
reads Harris's descent of the constant sheaf along the cover of level
`K(N, m)` as the published association to the finite geometric torsors
`Y m`: the input `Y` and `hY` play the role of the covers of
`S(GG, X_{n−1})_{K(N)}` with the finite groups `K(N)/K(N, m)`, and the groups
`U / ker(U → Aut(𝓛 / ℓ ^ m 𝓛))` play the role of these quotients. As
recorded in the published `HarrisEtaleCoefficients`, these kernels need not
be Harris's levels, the associated sheaves are not asserted to be the
particular sheaves of Proposition 4.4, and the supplied torsors are not
identified with Harris's Shimura levels. With `𝒪_m`
read as `𝒪 / ℓ ^ m 𝒪`, so that `𝓛_m = 𝓛 / ℓ ^ m 𝓛` (published
ReductionLattice), the inverse system of `harrisEtaleDivisibleSystem` is the
published model of Harris's `{𝓛̃_m}`, and the statement is that it carries an
`ℓ`-divisible structure.

In Harris `ℓ` is a rational prime and the coefficient place is the place `ℓ`
of `ℚ`. Here `ℓ` is any nonzero natural number and `p` any finite place of
`ℚ`; no relation between them is assumed. If `p` does not divide `ℓ`, then
`ℓ` is a unit in `R`, all the `𝓛 / ℓ ^ m 𝓛` vanish, and the statements hold
for the zero system (a remark, not formalized).

## Scope

The module constructs maps `i` and proves the `ℓ`-divisible system axioms for
the published étale coefficient system and, under the explicit hypothesis
`hΓ`, for its global sections. It does not construct Harris's Shimura
varieties, the covers of level `K(N, m)` or their torsor property (`Y` and
`hY` are inputs), the lisse `ℓ`-adic sheaf `W̃`, compactly supported or
derived cohomology of the system, the spectral sequences (4.4.1), (4.9) or
(4.10.4), or the Mittag-Leffler argument in the proof of Proposition 4.10.
It does not prove `hΓ`. The coefficient category is sheaves of modules over
the fixed ring `R`, on which `ℓ ^ m` acts by zero on `𝓛 m`; the freeness of
`T_m` over `ℤ/ℓ^m` in Harris's definition enters only through the published
reading of (2.1) as the field `flat`. The groups act on abstract objects:
there are no topologies, smoothness conditions or Galois actions.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
