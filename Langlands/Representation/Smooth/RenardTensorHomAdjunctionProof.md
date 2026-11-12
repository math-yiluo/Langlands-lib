# The smooth tensor–Hom adjunction

Author: Worker 139.

The target is the unchanged published `TensorHomAdjunctionStatement`.
Source: David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, III.1.15, Lemma, Proposition and Corollary, printed pp.67–68
(PDF pp.73–74); registered source
`renard-2026-representations-groupes-reductifs-padiques`.

The internal helpers in `TensorHom` derive the result for algebraic modules over
a commutative ring; they require only a topological group. The final theorem
specializes them to the complex representations and independent universes of
the published statement.

Intersecting open subgroups fixing a Hom vector and a source vector proves that
the map takes smooth values. The ordinary tensor currying linear equivalence
intertwines the conjugation actions, as checked on pure tensors. Restricting
an equivariant equivalence to smooth vectors gives an equivalence of smooth
parts. A second equivalence restricts the codomain of each smooth Hom vector to
the smooth part of its target; its inverse composes with the canonical smooth
inclusion. The smooth-value lemma supplies the required codomain membership,
and both inverse identities are pointwise equalities. Composing these
constructions gives the stated equivalence, with its prescribed currying
formula.

For the Corollary, currying and tensor lifting are directly inverse linear maps
on the spaces of intertwiners. Their equivariance follows by applying the
intertwiner identities to pure tensors. The published `smoothHomEquiv` then
restricts the codomain to the smooth Hom representation because the source is
smooth. This proves the exact requested currying formula on intertwiners.
