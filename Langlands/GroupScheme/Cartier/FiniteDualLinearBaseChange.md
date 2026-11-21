# Scalar extension of the finite projective dual

For a finite projective \(R\)-module \(M\) and an \(R\)-algebra \(S\),
`moduleDualBaseChange` identifies \(S\otimes_R M^*\) with the
\(S\)-linear dual of \(S\otimes_R M\). The finite projective
contraction equivalence first identifies the source with
\(\operatorname{Hom}_R(M,S)\). Extend these maps to the tensor by
sending \(t\otimes x\) to \(t\) times the value at \(x\), and restrict
along \(x\mapsto 1\otimes x\) for the inverse. The resulting equivalence
is \(S\)-linear and sends \(s\otimes f\), evaluated at \(t\otimes x\),
to \(stf(x)\) in \(S\).

`linearDualBaseChange` gives the same equivalence on the underlying
modules of the convolution duals. Specializing to a residue field at
any prime proves `rankAtStalk_dual`, since the dual of a finite
dimensional vector space has the same dimension.

Tate (1967), §1.2, printed p. 159 (PDF p. 1), constructs the Cartier
dual from the linear dual of the coordinate algebra and gives the
same order for the two finite groups. The Lean calculation proves
the underlying module equivalence and the corresponding stalk rank
identity.
