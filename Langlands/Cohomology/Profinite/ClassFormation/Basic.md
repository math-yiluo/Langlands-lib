# Class formations

`Langlands/Cohomology/Profinite/ClassFormation/Basic.lean`, namespace
`Langlands.ProfiniteCohomology`.

A class formation is a smooth module `C` over a topological group `G` together with, for every
open subgroup `U`, an isomorphism `inv_U : H²(U, C) ≅ ℚ/ℤ`, such that `H¹(U, C) = 0` for every
open `U` and `inv_V ∘ res = [U : V] · inv_U` for open `V ≤ U`. This is the axiomatic frame of
class field theory (Artin–Tate): the local theory feeds it with `C = L̄ˣ` and the invariant map
of the local Brauer group, the global theory with the idèle class group.

## Declarations

Restriction between subgroups.

- `continuous_subgroup_inclusion`, `subgroupInclusionOfLE h : V →ₜ* U` (for `V ≤ U`),
  `resResHom A h` (the identity of `A`, between the two restrictions to `V`) and
  `resOfLE A h n : Hⁿ(U, A) → Hⁿ(V, A)`, the restriction from `U` to `V` (`resOfLE_eq`).
- `resOfLE_comp`: restrictions compose. `continuous_subgroupOfEquivOfLe`,
  `continuous_subgroupOfEquivOfLe_symm`, `subgroupOfEquivOfLeSymmHom`, `subgroupOfEquivOfLeHom`
  (Mathlib's `Subgroup.subgroupOfEquivOfLe` as continuous homomorphisms), `resSubgroupOfHom`, and
  `resOfLE_eq_res_comp`: restriction from `U` to `V` is restriction to `V ∩ U` (a subgroup of `U`)
  followed by an isomorphism (`isIso_map_resSubgroupOfHom`); `resOfLE_apply_eq_zero_iff`.
- Instances `isSmoothRep_res_quotientToInvariants`, `isSmoothRep_res_res`.

General functoriality.

- `cochainsMap_congr`, `map_congr`: equal homomorphisms and pointwise equal coefficient maps give
  equal maps; `map_eq_id`.
- `resInvHom e f hf`, `resInvHom_hom_apply`, `resInvHom_hom_apply'`, and
  `isIso_map_of_mulEquiv`: a topological isomorphism `H ≃* G` with a bijective compatible
  coefficient map induces isomorphisms on cohomology.

Class formations.

- `H2Open C U`: `H²(U, C)` for an open subgroup `U`.
- `PreClassFormation C` (structure): additive maps `inv U : H²(U, C) → ℚ/ℤ` (here `QZ`, the
  discrete `ℚ/ℤ` of `Characters.lean`), `H¹(U, C) = 0` for all open `U`, and `inv_res`.
- `ClassFormation C` (structure): a pre-class formation whose maps `inv U` are bijective.
- `ClassFormation.At P C` (structure): a pre-class formation whose `inv U` are injective with
  image containing the `p`-primary part of `ℚ/ℤ` for `p ∈ P` (a class formation for the primes
  in `P`; used by the global theory). `ClassFormation.toAt`: a class formation is one for every
  set of primes.
- `ClassFormation.invEquiv F U : H²(U, C) ≃+ RationalModIntegers`: the invariant isomorphism with
  values in the Library's `Langlands.ClassFieldTheory.Local.RationalModIntegers`
  (`invEquiv_apply`), and `invEquiv_res`: `inv_V(res x) = [U : V] · inv_U(x)`.
- `ClassFormation.ofAddEquiv inv isZero_one inv_res`: a class formation from invariant
  isomorphisms with values in `RationalModIntegers`, vanishing `H¹` and compatibility with
  restriction; `invEquiv_ofAddEquiv`.
- `H2Quotient C U V`, `PreClassFormation.fundamentalClass F U V`: for `V` normal in `U`, the class
  of `H²(U/V, C^V)` whose inflation has invariant `1/[U : V]` (its properties are in
  `FundamentalClass.lean`).
- `PreClassFormation.resLE_eq_zero_iff`: when `inv V` is injective, the restriction of `x` to `V`
  vanishes iff `[U : V] · inv_U(x) = 0`.

- `injective_map_of_continuousMulEquiv m A n`: restriction along a topological isomorphism
  `m : H ≃ₜ* G` is injective on `Hⁿ` (from `isIso_map_of_mulEquiv`).

Complete type of `injective_map_of_continuousMulEquiv`, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.injective_map_of_continuousMulEquiv.{u} {k G H : Type u} [CommRing k] [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] (m : H ≃ₜ* G)
  (A : Rep.{u, u, u} k G) [Langlands.IsSmoothRep A] (n : ℕ) :
  Function.Injective
    ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map (↑m) (CategoryTheory.CategoryStruct.id (Rep.res (↑↑m) A)) n))
```

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/ClassFormationDefs.lean` and
`src/GroundTheory/ProfiniteCohomology/ClassFormations/IsIsoCohomologyMapAlongResSubgroupOfHom.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Names and notions replaced: `cohomologyResLE` → `resOfLE`; `ClassFormationAt` →
`ClassFormation.At`, `toClassFormationAt` → `ClassFormation.toAt`; the source's
`cohomologyMapAlong` with a homomorphism and a continuity proof → `map` with a bundled
`H →ₜ* G` (hence `subgroupInclusionOfLE`, `subgroupOfEquivOfLeHom`, `subgroupOfEquivOfLeSymmHom`
and the bundled forms of `cochainsMap_congr`, `map_congr`, `map_eq_id`); the source's
`isIso_cohomologyMapAlong_of_mulEquiv` → `isIso_map_of_mulEquiv`. The source's `invEquiv`
(to `QZ`) is replaced by `ClassFormation.invEquiv` with values in `RationalModIntegers`, and
`ofAddEquiv`, `invEquiv_res`, `invEquiv_ofAddEquiv` are new: they give the interface
"invariant as an additive isomorphism to the Library's `ℚ/ℤ`" while keeping the source's
structures, whose field `inv` is shared with `PreClassFormation` and `ClassFormation.At`.

`injective_map_of_continuousMulEquiv` contains no text of the source.

## References

- E. Artin, J. Tate, *Class Field Theory* (AMS Chelsea 2009, reprint with corrections of the 1967
  edition), chapter XIV, §1, Definition 1, pp. 143–144 (formations), §2, Axiom I, p. 147, and §3,
  Axiom II, p. 151 (class formations).
- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter XI,
  §1, pp. 164–166 (formations), and §2, Axioms I and II, pp. 166–167 (class formations).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §1, Definition (3.1.8), p. 156 (formation modules, class
  formations).

The three books state the axioms on the finite layers `U/V` (`V` open and normal in `U`):
`H¹(U/V, C^V) = 0`, and invariant maps, injective on the union of the `H²(U/V, C^V)`, that send
`H²(U/V, C^V)` onto the subgroup of order `[U : V]` of `ℚ/ℤ`; here the axioms are stated for the
cohomology of the open subgroups themselves, with `inv_U` an isomorphism onto all of `ℚ/ℤ`.
