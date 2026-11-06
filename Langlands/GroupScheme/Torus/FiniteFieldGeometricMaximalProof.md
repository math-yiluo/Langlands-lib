# Geometrically maximal tori over finite fields

Author: Worker 1442.

`Langlands.GroupScheme.finiteFieldGeometricMaximalTorus` proves the exact
published `FiniteFieldGeometricMaximalTorusStatement.{u}` for arbitrary
universe `u`. For every finite field `k : Type u` and smooth connected affine
group scheme `G` over `Spec k`, it gives a commutative group scheme `T` and
an actual inclusion `i : T.toGrp ⟶ G` that is maximal both over `k` and after
the specified pullback to `AlgebraicClosure k`. Both maximality witnesses
concern this same inclusion. The field hypothesis is `Finite k`, with no
chosen enumeration, characteristic restriction, or reductivity or splitness
assumption on `G`.

The implemented proof applies
`finiteFieldGeometricMaximalTorus_of_maximalTorusConjugacy`, imported from
`Torus.FiniteFieldGeometricAssembly`, to the published proof
`maximalTorusConjugacy`, imported from
`Absolute.MaximalTorusConjugacyProof`. The latter discharges the assembly's
entire remaining premise at the same universe.

The assembly first obtains a maximal torus over the algebraic closure.
Maximality under a field isomorphism and geometric conjugacy permit Lang's
construction of a Frobenius-stable conjugate. The coalgebra splitting theorem
and Frobenius descent then produce an inclusion over the original field,
recover its actual geometric pullback, and prove geometric maximality.
Independent faithfully flat reflection proves maximality over the original
field. A local `Fintype.ofFinite` supplies the enumeration used internally.
The conjugacy proof uses Borel conjugacy and solvable maximal-torus conjugacy,
with no structural premise left over.

This file is an internal composition of those published proofs; its proof
route and provenance are inherited from the named interfaces. The target
Lean/Markdown pair and its imports are unchanged. The dependency route avoids
the no-torus unipotence theorem and general forward preservation of maximal
tori under field extension; field-isomorphism transport and maximality
reflection are independent inputs.
