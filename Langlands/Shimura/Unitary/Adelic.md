# Actual topological and finite adelic similitude points

Author: Worker 57. This construction is a prerequisite of the arithmetic
specialization of the Harris level tower.

For a commutative ring `R`, an `R`-algebra `A` with `[Ring A]`, an involution
`σ : AlgebraInvolution R A`, and a commutative `R`-algebra `S`,
`σ.Points S` is the previously constructed similitude subgroup over the
actual scalar extension `S ⊗[R] A`, with a named carrier. Its algebraic
group structure requires neither topology nor module finiteness.

With only `[TopologicalSpace S]`, the topology on `σ.Points S` comes from
Mathlib's `moduleTopology S (S ⊗[R] A)`, the units topology recording both
value and inverse, and the product and subgroup topologies.
`Points.continuous_multiplier` requires only this coefficient topology:
the multiplier is projection onto the scalar-unit coordinate.

The `IsTopologicalGroup (σ.Points S)` instance additionally assumes
`[IsTopologicalRing S]` and `[Module.Finite R A]`. Finiteness passes to the
scalar extension as an `S`-module, and
`IsModuleTopology.isTopologicalRing S (S ⊗[R] A)` supplies the tensor
algebra's topological-ring structure before passing to units and the
subgroup. No topology on `R` or on the original algebra `A` is required.
Separately, `coordinateEquiv` assumes `[IsTopologicalRing S]` and a supplied
basis `b : Module.Basis ι R A` with `[Finite ι]`. It identifies the tensor
module topology with the ordinary finite product topology on `ι → S`.
There is no separate `Module.Finite R A` parameter in this declaration;
the finite basis supplies the relevant finiteness. No basis choice is
hidden in the definition of the topology.

For any commutative `R`-algebra `T`, `pointsMap` uses the actual tensor
coefficient map induced by `f : S →ₐ[R] T` and proves multiplier
compatibility without topological or finiteness assumptions.
`continuous_changeCoefficients` and `continuous_pointsMap` both assume
topologies on `S` and `T`, `[IsTopologicalRing S]`, `[IsTopologicalRing T]`,
`[Module.Finite R A]`, and `hf : Continuous f`. The proof uses the module
topology universal property, then the units and subgroup topologies.
`diagonalPoints` is an algebraic map from the original group to the scalar
extension by the tensor inclusion; its multiplier is the corresponding
scalar unit.

The rational specialization uses the published `Langlands.Global.FiniteAdeles`
and `FiniteCompletion` interfaces, hence actual restricted products and
completions. In particular the multiplier is a rational finite adele, rather
than independent multipliers over the totally real center. These
coefficient rings carry their actual topological-ring structures.
`continuous_finiteEvaluation` proves continuity of coefficient evaluation
without a finiteness assumption on `A`. The continuous point-group map
`finiteLocalMap` and its diagonal compatibility theorem
`finiteLocalMap_diagonal` assume `[Module.Finite ℚ A]`. Thus evaluation of a
diagonal rational point equals its direct local scalar extension.

The general base, algebra and coefficient carriers retain independent
universes. The topological-ring and finiteness assumptions occur at the
scopes listed above. In the Harris specialization, finiteness over `ℚ`
follows from the given central-simple finite-dimensional algebra over a
number field.

This is a derived implementation of the finite-adelic group and rational
diagonal appearing in Harris (1997), Section 2, printed pages 88-90, and
Harris (1999), Section 4, printed pages 308-309, with the rational multiplier
convention of Kottwitz (1992), printed page 654. These original passages
were read. The finite-module topology argument is provided by the pinned
Mathlib declarations, not asserted as a theorem from those articles.
In the pinned `Mathlib.Topology.Algebra.Module.ModuleTopology`,
`moduleTopology` needs only a coefficient topology, addition and scalar
action. `IsModuleTopology.isTopologicalRing` assumes a commutative
topological coefficient ring and a finite module algebra.
`continuous_of_linearMap` uses the module topology on its source and
continuous addition and scalar multiplication on its target;
`continuous_of_ringHom` uses a topological semiring target and continuity
on scalars. The coordinate argument also uses the module topology on a
topological ring itself and `IsModuleTopology.instPi` for a finite product.
No affine representability, adelic decomposition of a prescribed inner
form, compact-open subgroup existence, Shimura scheme, or local system
is asserted by this module.

Source fingerprints: Harris (1997), `harris-1997-drinfeld-cohomology`,
SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`;
Harris (1999), `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
Kottwitz (1992), `kottwitz-1992-lambda-adic-simple-shimura`,
SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
Formal dependencies are the published `Unitary.Similitude`, `Global.Adelic`,
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
