# Pullback of rigidified modules along a commuting square

For a commuting square with maps `ε : S → X`, `ε' : S' → X'`,
`f : X' → X`, `g : S' → S`, and `ε' ≫ f = g ≫ ε`, the construction
`Langlands.SchemeModule.RigidifiedModule.squarePullbackIso` gives the natural
isomorphism `g* ε* ≅ ε'* f*`. It composes Mathlib's constructed pullback
composition comparison, the equality comparison for the square, and the
inverse composition comparison.

Given an explicit isomorphism `unitIso : O_S' ≅ g* O_S`, `pullbackObj` sends
`(M, α)` to `f* M`, rigidified by the composite
`O_S' ≅ g* O_S ≅ g* ε* M ≅ ε'* f* M`.
`pullbackWithUnit` is the resulting functor between the categories of
rigidified modules. Its map on morphisms is the actual module pullback `f*`.
Naturality of `squarePullbackIso`, functoriality of `g*`, and compatibility of
the original morphism prove compatibility with the new rigidifications.
The identity and composition laws follow from the module pullback functor.
`pullbackWithUnitForgetIso` identifies the functor followed by forgetting with
forgetting followed by ordinary module pullback; the two functors are
definitionally equal.

## Provenance and scope

This is derived infrastructure for the pullback construction in Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft, Chapter VI §1,
paragraph (6.2), printed p.88 (PDF p.92), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source pulls back a rigidified line bundle along `id_X × h` and its
rigidification along `h`, using the section square. The present construction
isolates that operation for actual modules and any commuting square. It needs
neither a cartesian square nor a local-rank-one hypothesis.

The structure-module comparison is an explicit input. This module does not
construct its canonical choice, prove coherence under composition of squares,
or construct the relative Picard presheaf. Those require the canonical unit
comparison and further compatibility results. No group law, representability,
or assertion about automorphisms is made here.
