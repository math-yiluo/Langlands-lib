# Admissibility of upper refined Jacquet modules of product Levis

Author: Worker 828.

This module proves the published proposition
`Langlands.Parabolic.UpperRefinedJacquetAdmissibilityStatement.{uF,uV}`:
the actual normalized upper Jacquet module of an admissible product-Levi
representation along a block refinement is admissible. It is the upper
counterpart of the published
`Langlands.Parabolic.isAdmissible_refinedOppositeJacquetAction`, and the
proof follows that one. It uses the published upper canonical-lift
bijection `Langlands.Jacquet.refinedStableImageJacquetBijective` in place of
the opposite one.

## Declarations

- `Langlands.Parabolic.isAdmissible_refinedJacquetAction F T B S V`: for every
  admissible `ρ : Representation ℂ (B.Levi F.Carrier) V`, the unnormalized
  Jacquet action
  `Jacquet.action ρ (refinedUnipotent F.Carrier B S) (refinedLevi F.Carrier B S) _`
  is admissible.
- `Langlands.Parabolic.isAdmissible_normalizedRefinedJacquet F T B S V`: for
  every admissible `ρ`, the actual normalized refined Jacquet module
  `T.normalizedRefinedJacquet B S ρ` is admissible.
- `Langlands.Parabolic.upperRefinedJacquetAdmissibility`: the statement,
  obtained by introducing the quantified data and applying the previous
  theorem.

Here `F : PadicField p`, `T : F.TopologicalData`, `B` is a block shape of
rank `n`, `S : BlockRefinement B`, and `V` is a complex vector space in an
arbitrary universe. No finite-dimensionality of `V` is assumed.

## Proof

Smoothness of the Jacquet action is the published `Jacquet.isSmooth_action`.
Fix an open subgroup `L` of the refined Levi `M = refinedLevi F.Carrier B S`.
The proof finds a smaller subgroup whose fixed space in the Jacquet module is
finite-dimensional:

1. The subspace topology gives a neighbourhood `U` of `1` in `B.Levi F.Carrier`
   whose trace on `M` lies in `L`. The published
   `CuspidalSupport.exists_leviPiOpenSubgroup_subset` gives compact open
   subgroups `K i` of the blocks with block Iwahori factorizations for the
   inner refinements `S i`, whose product `KP` lies in `U`.
2. `BlockShape.deepChamberNonempty` chooses strictly contracting inner block
   scalars `a i`. The upper canonical-lift theorem
   `Jacquet.refinedStableImageJacquetBijective` states that the stable-image
   Jacquet map from the `KP`-fixed vectors of `ρ` to the `J`-fixed vectors of
   the Jacquet module, where `J` is `KP` pulled back to `M`, is bijective.
3. The `KP`-fixed space of `ρ` is finite-dimensional because `ρ` is
   admissible. Hence the `J`-fixed space of the Jacquet module is
   finite-dimensional, as the image of a surjective linear map.
4. Since `J ≤ L`, the `L`-fixed space is contained in the `J`-fixed space.
   It is finite-dimensional by `Module.Finite.of_injective` applied to the
   inclusion.

The normalized module is the twist of the unnormalized Jacquet action by the
inverse half character of the refined Levi modulus. That character has open
kernel (`Jacquet.isOpen_ker_inverseHalfCharacter` together with
`T.isOpen_ker_refinedLeviModulus`). The published `isAdmissible_twist_iff`
then transfers admissibility.

## Provenance and scope

This is the refined-Levi case of Casselman's Theorem III.5.6
(`casselman-2019-jacquet-module`, page 7): Jacquet modules of admissible
representations are admissible, by the canonical-lift argument of
Lemma III.5.4 and Proposition III.5.5. The Lean proof is a direct
transcription of the published opposite-Jacquet proof, using the upper lift.
It is used in
`Langlands.Representation.Classification.InductionWeakJacquetBoundsAssembly`
for the spectral extension step.
