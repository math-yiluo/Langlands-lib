# Bundling from multiplicative inversion

Author: Worker 133.

This module provides a conditional construction and reduction for the existing
`Langlands.AbelianScheme.SourceDefinitionEquivalence`. It does not prove that
statement without a hypothesis. The remaining geometric obligation is to show
that inversion is a monoid-object homomorphism whenever the structure morphism
is smooth, proper and geometrically connected.

`GroupScheme.isCommMonObj_of_inverse_isMonHom` works over every base scheme
and does not impose geometric hypotheses. A multiplicative inversion map gives
`(a⁻¹ * b⁻¹)⁻¹ = a * b` in every represented group of points, using
`MonObj.mul_comp`. The group inverse law identifies the left side with `b * a`.
Thus every represented group is commutative; Mathlib's
`isCommMonObj_iff_isMulCommutative` yields commutativity of the group object.

`AbelianScheme.ofIsAbelianOfInverseIsMonHom` combines that derived commutativity
with the three geometric hypotheses in `GroupScheme.IsAbelian`. Its underlying
group object is definitionally the supplied `G`, as the accompanying `toGrp`
lemma proves. No replacement group law or witness of commutativity is selected.

`sourceDefinitionEquivalence_of_inverse_isMonHom` uses this construction for
the forward direction of the existing proposition, under its explicitly
quantified hypothesis about inversion. In the reverse direction it substitutes
the equality of underlying group objects and applies `AbelianScheme.isAbelian`.
The reduction preserves the entire arbitrary-base and universe scope.

This is derived algebraic infrastructure for Lan, *Arithmetic compactifications
of PEL-type Shimura varieties* (2008 thesis), Corollary 1.3.1.7, printed p.108
(PDF p.148), which applies the preceding pointed-morphism rigidity corollary to
inversion. The implemented pointwise group argument spells out its algebraic
last step. The full arbitrary-base geometric rigidity is not supplied here.
Lan's Definition 1.3.1.1 (printed p.103/PDF p.143) and Corollary 1.3.1.6
(printed p.108/PDF p.148) use the geometric definition, without separately
assuming commutativity; Theorem 1.3.1.3 supplies the noetherian-reduction route.

Original source read: `lan-2008-arithmetic-compactifications-pel-thesis`,
SHA256 `c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd`,
PDF pp.143–148. The corresponding GIT Corollary 6.5, printed p.117/PDF p.130,
is restricted by that chapter to locally noetherian schemes and is not used
to extend the geometric result to arbitrary bases.
