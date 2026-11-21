# Detecting simple specializations on a compact projection

The coefficient maps and the surjective specialization \(q\) are linear
over a common operator ring. An idempotent \(P\) that sends each vector
into its cyclic submodule preserves the joint kernel of the coefficient
maps. The target \(Q\) is simple and has a map \(P_q\) satisfying
\(q(Px)=P_q(qx)\). Choose \(y\) in \(Q\) with \(P_q(y)\ne 0\).
If a vector in the joint kernel has nonzero specialization, simplicity
supplies an operator that sends its specialization to \(y\). Applying
that operator and then \(P\) produces a vector fixed by \(P\) in the
joint kernel whose specialization is \(P_q(y)\). This contradicts
detection on the fixed vectors of \(P\). The finite coefficient
subquotient lemma then gives a surjection from a submodule of the
coefficient space onto \(Q\).

`exists_subquotient_of_holomorphic_specialization` supplies detection
using scalar Taylor tests on a finite-dimensional space \(V\) of projected
sections. The scalar evaluations of the family of linear maps are
holomorphic on a common preconnected set containing both the base
parameter and an injective member. This gives one derivative order for all
sections whose scalar coordinates in \(V\) are holomorphic at the base
parameter. For a vector fixed by \(P\), the coefficient identities turn
vanishing of the indicated coefficients into vanishing of those scalar
derivatives. The corresponding section is then zero at the base
parameter, which by hypothesis forces zero specialization under \(q\).

This is an internal implementation of the finite-dimensional detection
and subquotient arguments in Langlands, *On the notion of an automorphic
representation* (1979), proof of Proposition 2 and Lemma 9, printed
pp. 205–207 (Corvallis Part I PDF pp. 200–202).
