# Reading the auxiliary stabilizer on the number field

Module `Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison`,
namespace `Langlands.Global.Harris`.

For a compatible place datum `P` for the tower `E ⊆ E' ⊆ L`, define the
character on `Lˣ` by applying `N_{L/E'}` and then evaluating the finite
component of `ξ` at `P.v'` on the resulting field unit.
`globalUnitComponent` is this evaluation of a single finite component on
field units, via the embedding into the completion.
`PlaceDatum.exactWeilStabilizer_iff_global` shows that, with normalized
reciprocity and the given component match, the local exact-stabilizer
condition is equivalent to the following test. An automorphism in
`Gal(L/E)` preserves this character on all of `Lˣ` if and only if it fixes
the image of `E'` pointwise. The comparison uses that `L/E` is Galois and
`P.vTilde` is the unique place of `L` above `P.v`.

## Implemented proof

1. `finitePlaceEquiv_liesOver` proves that contraction of a prime ideal
   commutes with transport through a commuting square of field
   isomorphisms. An automorphism over `E` therefore preserves `P.vTilde`.
   Extend it continuously to that completion using `finiteCompletionEquiv`.
   It fixes the base completion by density and transports along `P.isoTilde`
   to an automorphism of the local normal closure over `F`. This map on
   automorphisms is injective by restriction to `L`. The degree sum at the
   single place and `P.IsCompatible` identify the two finite Galois group
   cardinalities, giving surjectivity. The range clause of `P.IsCompatible`
   identifies the completion of `E'` with `F'`. Injectivity on field
   elements and density in the completion then identify the pointwise
   fixing conditions.
2. Put `M = galoisClosure F F'`. Restriction from the absolute Galois group
   to `Gal(M/F)` is continuous and surjective. Its composite with the dense
   Weil projection is surjective because this finite Galois group is
   discrete. The preimage of the automorphisms fixing `F'` is `W_{F'}` by
   the definition of `weilSubgroup`. The norm relation of normalized
   reciprocity writes the restricted Weil character on `W_M` as the
   character on `Mˣ` given by `χ ∘ N_{M/F'}`, composed with
   `reciprocityUnits`. The conjugation relation carries the action of
   `g⁻¹` to its restriction on `Mˣ`. Surjectivity of `reciprocityUnits`
   makes the stabilizer tests equivalent on these two groups.
3. Transport the determinant norm to the completed number-field tower
   using the compatible completion isomorphisms and use `P.HasComponent`.
   This expresses the character on `Mˣ` as the finite component of `ξ`
   after the completed norm from `L` to `E'`. There is a single place
   above `P.v'` by transitivity of lying over.
   `localUnitNorm_globalUnits` takes the `P.v'` coordinate of the adelic
   norm on principal elements and reduces its product to one factor.
   It identifies the completed norm on embedded field units with the
   embedded field norm. Field units are dense in the completed unit
   group, since the unit embedding into the completed field is open and
   the field itself is dense. Two continuous characters that agree on
   these units agree on the whole completed unit group.

## Imported results

- `HarrisUniquePlace` supplies the place-data setting from `HarrisSetup`,
  including `HasUniquePlaceAbove`, `PlaceDatum.IsCompatible` and
  `PlaceDatum.HasComponent`. Its imports supply the finite place and
  completion transport maps. `finitePlaceEquiv_mem` expresses transport
  by membership and `finiteCompletionEquiv_coe` gives compatibility
  with field elements. The fixing-subgroup and norm calculations use
  Mathlib's `IntermediateField.mem_fixingSubgroup_iff`,
  `Algebra.norm_eq_of_equiv_equiv` and its finite Galois theory.
- `FinitePlaceDegreeTransfer.finiteLocalDegree_sum` gives the sum of the
  completed degrees over the base place. The proof uses its one-factor case.
- `IdeleClassNorm.adeleNorm_principal` identifies the adelic norm of a
  diagonal element with the diagonal determinant norm. Its finite
  coordinate is the product of completed norms.
- `CommonClosureSurjectivity.reciprocityUnits_surjective` lets the test on
  the closure's Weil subgroup range over every completed field unit.
  The underlying `NormalizedReciprocity` and `closureRestriction` supply
  the reciprocity squares and the restriction used in the test.
- `Weil.Local.AssemblyProof` provides `localProjection_denseRange`.
  Mathlib's `InfiniteGalois.restrictNormalHom_continuous` and
  `AlgEquiv.restrictNormalHom_surjective` give the restriction to the
  finite Galois group.
- `Mathlib.Topology.Algebra.IsOpenUnits` supplies
  `Units.isOpenEmbedding_val`, used to pass from density of the field to
  density of its units.

This comparison is an intermediate result for the Mackey inheritance
proof. The exact stabilizer comes from Harris's condition (4.12) in the
proof of Lemma 4.7, printed p. 204 of *The local Langlands conjecture for
GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210.
The comparison with the norm character on the number field is derived
here using the compatible place data. The Mackey inheritance proof gives
the source of the inheritance argument.
[HarrisProposition48ExactStabilizerMackeyProof.md](HarrisProposition48ExactStabilizerMackeyProof.md)
