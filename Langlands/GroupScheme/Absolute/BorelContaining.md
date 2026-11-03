# A Borel containing a prescribed solvable subgroup

Worker 1358.

This internal construction extends the coordinate-height proof in
`Absolute.BorelExistence` to preserve a specified subgroup. It is a prerequisite
for the fixed-torus parabolic classification, rather than a proof of that
classification.

Let \(G\) be an affine group scheme locally of finite type over any field \(k\).
Suppose \(a:H\to G\) is a closed subgroup whose source is smooth, connected and
solvable in the published geometric-point sense. Then there are a Borel
embedding \(i:B\to G\) and an actual homomorphism \(f:H\to B\) such that
\(f i=a\). The construction `BorelExistence.borelContainingData` retains all
these objects, maps and properties.

Here “Borel” means exactly `IsBorelSubgroup`: maximal among smooth connected
solvable closed subgroups defined over \(k\). Over a field that is not
algebraically closed, this conclusion alone does not establish that its base
change is a Borel. No geometric maximality is asserted.

The implemented proof minimizes the finite height of the global coordinate
kernel among admissible subgroups through which \(a\) factors. This collection
is nonempty because it contains \(a\) itself. If the chosen subgroup factors
through a larger admissible subgroup, that larger subgroup still contains
\(H\), by composing the actual factor maps. Minimality and the existing
coordinate-kernel height criterion make this factor map an isomorphism. This
is precisely the maximality required by `IsBorelSubgroup`. The proof uses
`Nat.find` and the finite-height and isomorphism lemmas of
`Absolute.BorelExistenceCoordinates`; it requires no conjugacy, root datum,
reductive-group hypothesis or classification statement.

A commutative group scheme is solvable because its group of geometric points
is commutative. Published smoothness and connectedness of split tori therefore
give the corollary that a specified closed split torus lies in such a Borel,
over the original field. The index set of a split torus may be empty.

Finally, suppose this torus factors through a closed subgroup \(i:P\to G\).
The factor map into \(P\) is a closed immersion; \(P\) remains affine and
locally of finite type. Applying the corollary inside \(P\) gives a Borel
\(b:B\to P\), with an actual \(t:T\to B\), and both equations
\(tb=f\) and \((tb)i=a\). The result asserts that \(b\) is a Borel of \(P\).
It does not assert that \(bi\) is a Borel of \(G\), even when \(P\) is
parabolic. That promotion remains a separate structural obligation for the
fixed-torus classification.

If \(a\) is maximal as a torus of \(G\), its factor \(f:T\to P\) is maximal
in \(P\), by the published closed-subgroup transport theorem. The final
corollary packages the resulting \(b\) and the original \(f\) as
`IsBorelPair b f`. In particular, it preserves the specified torus and its
map, without conjugating or replacing them.

This is derived internal content: the added step is constrained minimization
in the existing coordinate-kernel argument. It makes no new claim quoted from
external literature.
