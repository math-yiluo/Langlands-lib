# Finiteness descent in filtered Cartesian ring diagrams

This is an internal algebraic prerequisite for the finite-morphism clause
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The categorical statement and the algebraic proof route are derived,
rather than a separately numbered assertion in the paper.

`FiniteTypeFinitenessDescent` uses two actual diagrams of commutative
rings on the same small filtered category, a natural transformation,
actual colimit cocones with their colimit witnesses, and a compatible map
of the colimit rings. At a chosen stage j₀, assume the component ring map
is of finite type and every square along an actual arrow out of j₀ is a
pushout. If the colimit map is finite, some component after an actual
arrow out of j₀ is finite. Here finite means finite generation of the
target as a module over the source via the specified ring map.

The intended argument lifts the finitely many coefficients of a monic
relation from a filtered colimit. Equality with zero descends to a later
stage. Apply this to a finite algebra-generating set, then take a common
stage. The pushout condition implies that the transported generators
generate the final component over its source; their integrality makes
that component a finite module. This uses neither injectivity of any ring
map nor a noetherian, reduced, domain, or finite-presentation assumption.
All rings and the indexing category share arbitrary universe u.

The paired Lean file defines the proposition only. Its proof and the
scheme-level relative finiteness and original-ring specializations are
separate obligations.
