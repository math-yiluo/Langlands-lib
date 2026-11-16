# The Weyl group scheme of a maximal torus is finite étale

Worker 588.

`Langlands.GroupScheme.weylGroupSchemeFiniteEtale` proves the unchanged
`Langlands.GroupScheme.WeylGroupSchemeFiniteEtaleStatement.{u}` for every
universe `u`. Its hypotheses are exactly a reductive group scheme `G` over an
arbitrary scheme `S`, a commutative group scheme `T`, and a closed homomorphism
`t : T.toGrp ⟶ G` that is a relative torus and is maximal on every residue-field
fibre. The conclusion supplies closed representatives of the actual all-test
normalizer and centralizer, together with their finite étale group-scheme
quotient and a flat, surjective, locally finitely presented quotient map with
the stated all-test kernel.

This is an internal composite proof using three published theorems.

First, reductivity gives `Smooth G.X.hom` and `IsAffineHom G.X.hom`.
[`smoothAffineTorusWeylQuotient`](SmoothAffineWeylQuotientProof.md) supplies
`N`, `n`, `Z`, `z`, `W` and `q`, with the closed representing properties,
separatedness, quasi-compactness and étaleness of `W → S`, the three required
properties of `q`, and the exact kernel condition on every `S`-scheme.

Next, [`weylQuotientFinitenessReduction`](WeylQuotientFinitenessReduction.md)
applies to these same `N`, `n`, `W` and `q`. Its general finiteness premise is
discharged by
[`Langlands.AlgebraicGeometry.etaleLocalCardinalityFiniteness`](../../AlgebraicGeometry/EtaleLocalCardinalityFinitenessProof.md).
The reduction uses reductivity and fibrewise maximality to obtain constant
geometric lift counts on a torus splitting cover. The general criterion gives
finiteness on that cover, and fppf descent gives `IsFinite W.X.hom`. The chosen
cardinality precedes all algebraically closed field and algebra-structure
tests over each local base.

Finally, the proof returns the original representatives and quotient map,
inserting this finiteness proof alongside their existing étaleness and other
properties in the target conjunction order. Thus the actual all-test
normalizer, centralizer and kernel identities are preserved. No additional
geometric, finiteness or noetherian hypothesis is introduced.

The original-source correspondence belongs to the unchanged
[`WeylGroupSchemeFiniteEtaleStatement`](WeylGroupSchemeFiniteEtaleStatement.md),
which derives its formulation from Conrad, *Reductive group schemes* (2014),
Proposition 3.2.8 and the general quotient theorem. This module assembles the
published quotient construction, local-base finiteness theorem and reductive
reduction rather than giving a new translation of those source statements.
