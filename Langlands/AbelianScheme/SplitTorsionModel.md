# Descent of an abelian scheme with split geometric torsion

An abelian scheme over a field with trivial monodromy at one finite invertible torsion level has a
model over a finitely generated subalgebra with invertible level. All points in the specified
geometric fibre are values of relative points over one larger finitely generated subalgebra.

## Lean statement and proof

`SplitTorsionModelStatement` takes an abelian scheme \(A\) over a field \(K\), a geometric point
\(s\) of its base, and a positive invertible torsion order \(n\). Its hypothesis says that the
pointed finite étale fundamental group acts trivially on the actual torsion module at \(s\).
It produces finitely generated \(\mathbb Z\)-subalgebras \(C\subset D\subset K\) and an abelian
scheme \(A_0\) over \(C\) whose base change is isomorphic to \(A\). The order \(n\) is invertible
in \(C\). For each point of the geometric fibre of \(A_0[n]\) at the composite point over \(C\),
a relative \(D\)-valued point restricts to the given point.

`splitTorsionModel` first applies `subalgebraDescent` and adjoins the inverse of \(n\).
`PolarizedFiniteLevel.levelIsoLinear` transports the action through the model isomorphism, and
`Tate.levelBaseChange_monodromy` transports it to the multiplication-kernel fibre over \(C\).
The restriction of this action to the fundamental group over \(K\) fixes the fibre. After
pullback to \(K\), `sectionOfFixedGeometricLift` produces a section through each point. The
relative points obtained this way form a finite family, to which `finiteFieldPointDescent`
applies.

## Source

This is an abelian-scheme formulation of the finite-data step in Deligne, *Résumé des premiers
exposés de A. Grothendieck*, SGA 7 I, Exposé I, Variante 1.3, pp. I-6 to I-7. It uses the
trivialized prime level to spread out the variety together with sections of that level. The
Lean statement allows any positive invertible torsion order with trivial action.
