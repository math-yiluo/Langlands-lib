# Proof: outer forms of type A are special unitary groups of algebras with involution

Module: `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraPresentationProof`.

The theorem `Langlands.GroupScheme.outerTypeAUnitaryAlgebraPresentation` proves the
published proposition `Langlands.GroupScheme.OuterTypeAUnitaryAlgebraPresentationStatement.{u}`
at every universe `u`. It has no hypotheses. The statement and its Markdown are imported
unchanged. The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is proved

Let `K` be a field and `G` an affine, locally finite-type, simply connected, absolutely
almost-simple group over `K` whose actual index has type `A_n` and whose actual star action
moves some simple vertex. Then there are a separable quadratic extension `E/K`, a central
simple `E`-algebra `B` of dimension `(n + 1)^2` that is a `K`-algebra through `E`, a
`K`-linear involution `τ` of `B` acting on `E` by the nontrivial automorphism of `E/K`, and
natural group isomorphisms `G(R) ≅ SU(B, τ)(R)` for all commutative `K`-algebras `R`
(`UnitaryAlgebra.Presentation E τ G`). The field and its characteristic are arbitrary. In
the proof, `E` is the image of the star field in the Galois splitting field, `B` is the
twisted Galois descent of the matrix algebra and `τ` is induced by an outer automorphism.

## The proof

The proof is a term that composes two results.

1. `specialLinearTitsCocycle`, in module
   `Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleProof`, proves
   `SpecialLinearTitsCocycleStatement.{u}`: a finite Galois splitting extension, a local
   isomorphism from `SL_(n+1)` to `G`, and Galois discrepancy matrices with the inner or outer
   formula according to the Tits star action.
2. `OuterTypeAUnitaryAlgebra.outerTypeAUnitaryAlgebraPresentation_of_specialLinearTitsCocycle`,
   in module `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraReduction`,
   proves `SpecialLinearTitsCocycleStatement.{u} → OuterTypeAUnitaryAlgebraPresentationStatement.{u}`.
   The discrepancy matrices form a twisted unitary cocycle; its descended algebra `B`
   (module `Langlands.LinearAlgebra.UnitaryTwistedChart`) is central simple over the star
   field with a unitary involution `τ`; explicit charts identify `SU(B, τ)` with `SL_(n+1)`
   at every cover point; and the resulting Galois-invariant local isomorphisms from the group
   scheme `SU(B, τ)` (module `Langlands.GroupScheme.Examples.UnitaryAlgebraGroupScheme`) to
   `G` descend to an isomorphism, which gives the presentation.

The module adds no other declarations.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998), Theorem (26.9), printed
p. 366: the functor `(B, τ) ↦ SU(B, τ)` is an equivalence onto simply connected absolutely
simple groups of type `A_n`; the theorem proved here is the outer-type part of its essential
surjectivity, as stated in the Markdown of the statement. The Lean proof does not follow the
book's route through the equivalence of groupoids; it descends the matrix algebra directly
along the Tits cocycle.
