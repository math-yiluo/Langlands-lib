# Admissibility of actual normalized opposite Jacquet representations

Author: Worker 166.

This module states
`Langlands.Parabolic.NormalizedOppositeJacquetAdmissibilityStatement.{uF,uV}`.
It is a closed proposition defined as the conjunction of five closed
propositions, in the order below. This module supplies statements, not proofs.

## Parameters and admissibility

Each clause quantifies over a prime `p`, a p-adic field `F : PadicField p`,
its supplied compatible `T : F.TopologicalData`, a natural rank `n`,
an ordered block shape `B`, and a complex representation on a carrier
`V : Type uV`. The field universe `uF` and carrier universe `uV` are
independent. The refined clauses additionally quantify over every
`S : BlockRefinement B`. The only representation hypothesis is
`IsAdmissible ρ`. Rank zero, with the empty block shape, is included.

The installed topology is exactly `T.topology`. All matrix, product-Levi and
subgroup topologies in the conclusions are the induced topologies of the
existing constructions. `Langlands.IsAdmissible` means smoothness and
`Module.Finite ℂ` for the fixed submodule of every open subgroup. Over `ℂ`
this is finite dimensionality of each fixed space. The carrier itself can
be infinite dimensional.

## The five clauses

1. `StandardOppositeJacquetAdmissibilityStatement` starts with an admissible
   representation `ρ` of `GL_n(F)` and concludes admissibility of the exact
   bundled representation
   `CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of ρ)`.
   Its carrier is the actual coinvariant quotient by
   `B.oppositeUnipotentSubgroup F.Carrier`. The quotient action of the
   embedded block-diagonal Levi is pulled back along
   `B.leviEquiv F.Carrier` to the product group `B.Levi F.Carrier`.
   No new action or implicit equivalence witness is introduced.
2. `RefinedOppositeJacquetAdmissibilityStatement` starts with an arbitrary
   admissible representation of `B.Levi F.Carrier` and concludes
   admissibility of `T.normalizedRefinedOppositeJacquet B S ρ` on
   `Geometric.refinedLevi F.Carrier B S`. Its carrier is the quotient by
   `Geometric.refinedOppositeUnipotent F.Carrier B S`, the product of the
   actual inner lower radicals.
3. `ComposedOppositeJacquetAdmissibilityStatement` starts with an admissible
   representation of `GL_n(F)` and concludes admissibility of
   `T.normalizedComposedOppositeJacquet B S ρ` on the same refined subgroup.
   Its carrier is the quotient by
   `Parabolic.composedOppositeUnipotent F.Carrier B S`, which includes the
   outer lower radical and the embedded inner lower radical.
4. `FlattenedRefinedOppositeJacquetAdmissibilityStatement` concludes
   admissibility of the representation in clause 2 pulled back along the
   exact homomorphism
   `(Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom`.
5. `FlattenedComposedOppositeJacquetAdmissibilityStatement` concludes the
   corresponding pullback admissibility for clause 3.

In the last two clauses the acting group is `(B.flatten S).Levi F.Carrier`.
The carrier is unchanged by pullback. The homomorphism is the underlying
homomorphism of the published continuous multiplicative equivalence
`Geometric.flattenedLeviEquivContinuous`. Thus these two consumer interfaces
are the coordinate-transport consequences of clauses 2 and 3, using
`isAdmissible_comp_continuousMulEquiv` from `CuspidalSupport.GroupTransport`.
Continuity is provided by that constructed equivalence; it is not an
additional assumption on the input. This module states these consequences
explicitly rather than providing their proofs.

## Normalization

All three quotients use the positive upper half-modulus on the lower radical.
For the standard clause, `oppositeJacquet` forms the upper full character
on the embedded Levi by composing `T.leviModulus B` with
`(B.leviEquiv F.Carrier).symm`, inverts this full character, takes its
inverse half through `Jacquet.normalizedActionOfModulus`, and pulls the
action back to the product Levi. Hence the scalar on a quotient class is
the positive half of the upper block character.

For the refined and composed clauses, the full opposite characters are
respectively `(T.refinedLeviModulus B S)⁻¹` and
`(T.composedLeviModulus B S)⁻¹`. The existing
`inverseHalf_refinedOppositeLeviModulus` and
`inverseHalf_composedOppositeLeviModulus` identify the normalizing scalars
with `T.refinedLeviHalfModulus B S` and
`T.composedLeviHalfModulus B S`. The composed character includes both the
outer and inner contributions. The statements use these existing actions
literally and retain their explicit residue-normalized determinant characters.

## Original source and derived formulation

The original source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained file is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Pages 1–7 were read; the normalization and theorem formulas on pages 4 and 7
were also inspected as images. No separate project errata note was found.
The warning in the original after III.5.7 was checked.

Page 1 fixes the setting of rational points of a connected reductive group.
Section III.3, pages 3–4, defines the actual quotient by radical differences
and normalizes its Levi action by the inverse half of the parabolic modulus.
Lemma III.5.4 on page 6 and Proposition III.5.5 on page 7 provide the
canonical-lift argument. Theorem III.5.6 on page 7 concludes that the Jacquet
module of an admissible representation is admissible. Page 7 restricts the
coefficient ring to a field before these last two results and warns that an
earlier claimed Noetherian-ring extension had an incorrect proof. The present
statements use only complex coefficients.

The five-clause formulation is derived from this general admissibility
theorem, specialized to the opposite block parabolic in `GL_n`, to the
product of inner opposite parabolics in the outer product Levi, and to the
full composed opposite parabolic in `GL_n`. The product-Levi specialization
concerns arbitrary admissible representations of that reductive product;
it does not presume a tensor decomposition. The flattened clauses transport
along the actual continuous equivalence described above. The source does not
use the project's block indices, bundled representations or universe
parameters; those are internal formalization choices. The rank-zero case
is the trivial-group instance, where the quotient and its character are
trivial. These specializations and transports remain proof obligations.

No irreducibility, finite length, finite-dimensional carrier, tensor
factorization, chosen canonical lift or compatibility certificate is a
hypothesis. The module makes no assertion of second adjointness, exactness,
transitivity, a cuspidal count, generic comparison or an irreducible head.
