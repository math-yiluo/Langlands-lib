# Associated coefficient sheaves over an object with a group action

Author: Worker 57.

For a Grothendieck site with binary products, an actual object `Y` with a group
action, and an actual module-valued coefficient sheaf `F` with a group action,
this module constructs the invariant subsheaf of `U ↦ F(Y × U)`. The
diagonal operator combines pullback by the inverse deck transformation with
the coefficient operator. Thus its invariant sections are the equivariant
sections over the cover. No output sheaf, descent isomorphism, or local
triviality theorem is supplied as an input.

`productSheaf` uses Mathlib's localization topology and the proved continuity
of `Over.star` to construct a sheaf. `deckMap` is the actual restriction along
the product of a cover endomorphism with the identity. Its composition and
naturality certificates yield the diagonal group action. The construction
is functorial in equivariant coefficient maps. `inclusion_natural` proves
compatibility of these maps with the invariant inclusion. `associatedFunctor` takes
the actual categorical limit of the single-object group diagram in the
category of module sheaves. The projection satisfies invariance, is monic,
and has the proved universal lifting and uniqueness property. For constant
coefficients the existing constant-sheaf functor is applied first.

The site object and morphism universes are independent. The coefficient ring,
coefficient module carriers and group use universe `u`, which supplies the
required small limit. The construction does not enlarge the module universe
to the universe of all site objects. This matters for the large small-etale
category of a scheme. No finiteness of the group is required merely to form
the invariant sheaf.

This is derived infrastructure for Harris 1999, Section 4, printed page 311
(PDF page 13). The paragraph following (4.8) descends the constant étale
sheaf of the deeper level `K(N,m)` to a lisse sheaf on the level `K(N)`,
using the finite deck group acting on both the cover and the coefficients.
The paragraph preceding Proposition 4.10 forms the inverse system of these
descended finite coefficient sheaves. The integral coefficients are the
stable lattices of Section 3, printed pages 307-308. These original passages
were read by Worker 57. Source ID
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
The explicit invariant-limit presentation and its proofs are the author's
categorical implementation, not a verbatim definition in that paragraph.

A genuine covering torsor and a proof of its local trivialization are needed
to identify this invariant sheaf with a locally constant sheaf of the given
rank. Neither arbitrary group actions nor arbitrary cover objects are
declared to have that property. The Harris scheme levels, finite torsor
certificates, stable lattices, and comparison of coefficient reductions
remain separate obligations. This file alone does not complete coefficient
descent in the assigned Harris geometry.

Formal sources are Mathlib 5ed2965256430c3649e86755f9576b54eca72435 under
Lean 4.34.0: `Sites.Over`, `Sites.ConstantSheaf`, `Sites.Limits`,
`ModuleCat.Sheaf`, `ModuleCat.Limits`, and `Action.Basic`. All intrinsic proofs and source in
this module are by Worker 57.
