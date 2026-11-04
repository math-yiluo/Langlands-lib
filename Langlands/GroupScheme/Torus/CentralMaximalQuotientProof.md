# The quotient by a central maximal torus contains no torus

Worker 1467.

`Langlands.GroupScheme.centralMaximalTorusQuotientStatement` proves exactly
`CentralMaximalTorusQuotientStatement.{u}` for an arbitrary universe `u`.
For an arbitrary field `k`, a smooth affine group scheme `H`, a central
maximal closed torus `j : Z.toGrp ⟶ H`, and an actual fppf quotient
`q : H ⟶ Q` whose scheme-theoretic kernel has range `SubgroupFunctor.range j`,
every homomorphism `g : T.toGrp ⟶ Q` from a torus has
`SubgroupFunctor.range g = ⊥`. This is triviality on points over every test
scheme. The proof adds no hypothesis to the published proposition: in
particular, it does not assume that `H` is connected, that `Q` is smooth or
affine, or that the field is perfect or has a specified characteristic.

The Lean proof applies Worker 1395's
[`centralMaximalTorusQuotientReduction`](CentralMaximalQuotientReduction.md)
to the exact structural theorems
[`centralTorusExtensionStatement`](CentralExtensionProof.md), authored by
Worker 1395, and
[`torusImageClosedTorusStatement`](ImageProof.md), authored by Worker 1358.
There are no residual structural premises in the entry theorem.

The reduction forms the actual pullback `E = T ×_Q H`. Its projection to
`T` is an affine fppf quotient with the original central torus as kernel;
affineness follows from the affineness of `H`, with no affine hypothesis on
`Q`. The central-extension theorem makes `E` a torus. The image theorem
factors `E → H` through a closed torus containing `Z`. Maximality identifies
this torus with `Z`, so its composite into `Q` is trivial. The flat
surjective projection `E → T` is an epimorphism of schemes, and cancellation
then makes `g` trivial. The reduction translates this into the asserted
bottom range on every test scheme. The entry theorem only supplies the two
proved inputs to this existing reduction.

The provenance is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 17.82, printed p.379 (one-based PDF
p.395), using Lemma 16.43, printed p.340 (PDF p.356), as explained in the
[published statement](CentralMaximalQuotientStatement.md). The implemented
pullback, central-extension and closed-image route is the internal
alternative formalized by the reduction; it does not use the statement
Markdown's identity-component argument. The extension proof's companion
explains its Hopf-algebra route and the image proof's companion explains
its splitting-field comparison. Thus the entry uses proved Lean inputs
rather than assuming the literature's structural results.
