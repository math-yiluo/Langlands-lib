# Renard's two Mackey natural isomorphisms

Source: Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.11 Theorem and its proof displays
(III.2.11.1)–(III.2.11.10), printed pp.82–83 / PDF pp.88–89.

`MackeyIsomorphismStatements` is a closed proposition for any continuous
homomorphism `φ : H → G` of Hausdorff locally compact nonarchimedean groups,
with their actual left Haar Hecke algebras. Neither injectivity nor closed
image of `φ` is required.

The conclusion first supplies equivalence proofs `eG`, `eH` for the exact
published smooth-to-Hecke functors. These are conclusions, rather than
additional assumptions restricting the theorem. They allow the definitions
of the transported actual Hecke functors `smoothI`, `smoothP`, `smoothF`
and `smoothPseudoF` to be used. The conclusion also identifies continuous
pullback `Fφ` naturally with `smoothF`.

The first Mackey isomorphism is unconditional:

`Hom(V,I(W))₀ ≅ I(Hom(Fφ(V),W)₀)`.

Lean expresses it as a natural isomorphism `mackeyHomLeft ≅ mackeyHomRight`
on `SmoothRep(G)ᵒᵖ × SmoothRep(H)`. Thus it is natural in `W` and
contravariantly natural in `V`. The Hom is exactly the existing smooth
part of `Representation.linHom`, and `I` is the smooth transport of the
actual Chapter I Hecke Hom induction.

The second assertion retains the source's additional hypothesis:

`Nonempty (smoothPseudoF ≅ smoothF)` implies
`P(W) ⊗ V ≅ P(W ⊗ Fφ(V))`.

It is expressed as a natural isomorphism of the two tensor model functors
on `SmoothRep(H) × SmoothRep(G)`, so it includes naturality in both
variables. The tensor products are the actual diagonal
`Representation.tprod`, and `P` is the smooth transport of the actual
Chapter I balanced tensor induction. The premise is an isomorphism of
functors, not unrelated objectwise identifications or an omitted condition.
It is precisely the condition used to justify (III.2.11.8) in the source.

The group universes `uG`, `uH` and carrier parameter `v` are independent.
The common carrier universe `max uG v` is stable under the actual tensor
and Hom induction constructions.

This file states the theorem. It does not construct the comparison maps or
prove any implication. The source's displays (III.2.11.1)–(III.2.11.10)
describe its proof route through the tensor–Hom and induction adjunctions;
those intermediate display equivalences are not separately asserted by
this focused statement. Proofs belong to separate tasks after publication.
