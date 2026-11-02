# Additive cocycles and exact-sequence closure

Author: Worker 148.

This internal algebraic module continues the published flat-test cobar
criterion. The rings B and C lie in Type u, C has the given source B-algebra
structure, and t : B → C is the separate target map. The modules lie in an
independent Type v. All coactions, morphisms and cocycles use the published
definitions unchanged.

`oneCocycles θ` is the additive subgroup of C ⊗[B] M consisting of the
elements satisfying `θ.IsOneCocycle`. The defining pointwise equation is
additive, so zero, sums, negatives and differences satisfy it. Tensor
naturality and composition naturality show that a morphism of coactions
sends cocycles to cocycles. Invariant preservation is already available
as `IsHom.mapsTo_invariants` in the published `GroupoidCoactionInvariants`
module.

`oneCohomologyVanishes_of_retract` assumes comodule morphisms i : M → N and
p : N → M with p ∘ i = id. If cocycles vanish in N, send a cocycle x in M
through C ⊗ i, write its image as δ(n), and apply C ⊗ p. Naturality gives
δ(p(n)) = x. This argument does not require flatness of C.

`oneCohomologyVanishes_of_shortExact` assumes C is flat over B and a short
exact sequence M → N → P of comodule morphisms. If the cocycles vanish in
M and P, they vanish in N. Project a cocycle x to P and write that image as
δ(q). Choose n mapping to q. Then x − δ(n) lies in the tensor kernel.
Flat exactness lifts it to z in C ⊗ M. Injectivity of the kernel map, after
tensoring with every flat test algebra, reflects the cocycle equation to z.
Write z = δ(m); then x = δ(n + i(m)).

These constructions and proofs are derived from the existing cobar
naturality lemmas, elementary additive identities and Mathlib's
`Module.Flat.lTensor_exact`. They are closure lemmas for a sufficient
vanishing condition. The geometric vanishing theorem, the construction of
kernel and quotient coactions, and Noetherian dévissage remain separate
steps.
