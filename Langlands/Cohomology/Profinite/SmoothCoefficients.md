# Smooth coefficient modules

`Langlands/Cohomology/Profinite/SmoothCoefficients.lean`, namespace `Langlands`.

The coefficients of the cohomology of a topological group `G` (in particular of a profinite
group, such as a Galois group) are the *smooth* representations: objects `A` of Mathlib's
`Rep k G` in which every vector is fixed by an open subgroup. This is the Library's
`IsSmooth A.ρ` (`Langlands/Representation/Smooth/Definitions.lean`); for a profinite group these
are the discrete `G`-modules of Serre and of Neukirch–Schmidt–Wingberg. The file turns the
property into a class, so that the constructions of the cohomology theory (restriction,
quotients, tensor products, …) receive it by instance search.

## Declarations

- `vectorStabilizer ρ v`: the subgroup of the `g ∈ G` with `ρ g v = v`; `mem_vectorStabilizer`
  unfolds membership. Lemmas: the stabilizer of `0` is everything; the stabilizer of `a + b`
  contains the intersection of those of `a` and `b`; that of `r • a` contains that of `a`; the
  stabilizer of `ρ g a` is the conjugate of that of `a`; for a trivial representation every
  stabilizer is `G`; a morphism of representations enlarges stabilizers, and an injective one
  preserves them.
- `mem_invariants_comp_subtype_iff`: `a` is invariant under a subgroup `U` iff `U` lies in the
  stabilizer of `a`; `invariants_comp_subtype_antitone`: invariants of a larger subgroup are
  invariants of a smaller one.
- `IsSmoothRep A` (class): `IsSmooth A.ρ`. `isSmoothRep_iff`, `isSmoothRep_iff_smoothRepProperty`
  restate it.
- `SmoothRep.isSmoothRep`: the underlying representation of an object of the Library's category
  `SmoothRep k G` is smooth; `IsSmoothRep.toSmoothRep A` bundles a representation with the
  instance as an object of `SmoothRep k G`.
- `IsSmoothRep.of_isOpen_stabilizer`, `IsSmoothRep.isOpen_stabilizer`,
  `isSmoothRep_iff_isOpen_stabilizer`: for a topological group, `A` is smooth iff the stabilizer
  of every vector is open.
- `Continuous.DiscreteModule.isSmoothRep`: the underlying representation of a discrete module of
  `Langlands.Continuous` (a discrete topological module with jointly continuous action, the
  coefficients of `Langlands/Cohomology/Continuous`) is smooth.
- Instances and criteria: every representation of a discrete group is smooth; trivial
  representations and subsingleton modules are smooth; smoothness passes to the source of an
  injective morphism, to the target of a surjective one and along isomorphisms; a module in
  which every vector is invariant under some open subgroup is smooth; restriction along a
  continuous homomorphism (`IsSmoothRep.res`, `isSmoothRep_res` for `H →ₜ* G`,
  `isSmoothRep_res_subtype` for a subgroup); subrepresentations and quotients; binary and finite
  biproducts, direct sums and products; the tensor product of two smooth representations
  (`isSmoothRep_tensor`) and the unit object of `Rep k G`; the first and third terms of a short
  exact sequence with smooth middle term; the invariants of a normal subgroup `N` as a
  representation of `G ⧸ N` (`isSmoothRep_quotientToInvariants`).
- `isSmoothRep_iff_smoothVectors_eq_top`, `hom_mem_smoothVectors`,
  `mem_smoothVectors_of_isSmoothRep`: the link with the Library's submodule `smoothVectors`.
- `isLocallyConstant_apply`: for a smooth `A` and `a ∈ A`, the map `g ↦ ρ g a` is locally
  constant. This is what makes the differential of a locally constant cochain locally constant.
- `isSmoothRep_iff_forall_exists_openNormalSubgroup`: for a compact group, `A` is smooth iff
  every vector is invariant under an open normal subgroup.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/DiscreteModules.lean`,
`src/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean`
and the first section of `src/GroundTheory/ProfiniteCohomology/CohomologyFunctoriality.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Notions replaced: the source's class `GroundTheory.ProfCoh.IsDiscreteRep` (open stabilizers) is
replaced by `IsSmoothRep`, a class wrapping the Library's `IsSmooth`; the source's `stabilizer`
by `vectorStabilizer` (Mathlib's `Representation.stabilizer` is in a module the Library does not
import); the source's `DiscreteRep` (full subcategory) by the Library's `SmoothRep`; the
source's `smoothSubmodule` and `smoothSubrep` by the Library's `smoothVectors` and
`SmoothRep.smoothPartObj`; the source's instances that the property is closed under subobjects,
quotients, finite products and that `DiscreteRep` is abelian by the Library's instances in
`Langlands/Representation/Category/Abelian.lean`. Source declarations and their names here:
`stabilizer` → `vectorStabilizer`, `mem_stabilizer` → `mem_vectorStabilizer`,
`stabilizer_zero`, `inf_le_stabilizer_add`, `stabilizer_le_stabilizer_smul`,
`coe_stabilizer_apply`, `stabilizer_eq_top_of_isTrivial`, `stabilizer_le_stabilizer_hom`,
`stabilizer_hom_of_injective` (with `stabilizer` → `vectorStabilizer` in the name),
`isOpen_stabilizer` → `IsSmoothRep.isOpen_stabilizer`, `isDiscreteRep_iff` →
`isSmoothRep_iff_isOpen_stabilizer`, `IsDiscreteRep.res` → `IsSmoothRep.res`,
`isDiscreteRep_quotientToInvariants_of_normal` → `isSmoothRep_quotientToInvariants`, the source's
`isDiscreteRep_tensor` (from `CupProducts.lean`) and `isDiscreteRep_tensorUnit` (from
`CupProducts/Cocycles.lean`), and in general `IsDiscreteRep`/`isDiscreteRep` →
`IsSmoothRep`/`isSmoothRep` in the names. The proofs of the instances for biproducts, direct
sums, products and tensor products are rewritten on `IsSmooth`.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.1, p. 10 (discrete `G`-modules: `A = ⋃ A^U`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §1, Proposition (1.1.8), p. 7 (equivalent descriptions of
  discrete `G`-modules), and p. 8 (direct sums and tensor products).
