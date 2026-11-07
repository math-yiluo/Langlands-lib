# Normalized dual integrals and the Hopf antipode

This internal derived unit works with a commutative Hopf algebra over a field.
Given a coordinate integral t with a t = counit(a) t and a linear functional
lambda with (id tensor lambda) Delta(a) = lambda(a) 1 and lambda(t) = 1,
it constructs F(a) = (id tensor lambda)((1 tensor a) Delta(t)). Tensor
linearity identifies id * F with contraction of Delta(a t), which is the
convolution unit by the two integral identities and the normalization.
Uniqueness of the convolution inverse of the identity proves F is the actual
antipode.

A left integral in the full convolution dual supplies the required tensor
contraction identity because the full linear dual separates vectors over a
field. If the antipode is involutive, evaluating any distribution on F(a)
expresses it as convolution evaluation at t against b -> lambda(a b).
Consequently, vanishing of all such convolution evaluations implies that the
distribution is zero. No finite dimension, cocommutativity, coordinate choice,
or existence of the supplied integrals is assumed or asserted.

The proof is derived from the Hopf inverse axioms and linear tensor algebra in
Mathlib. It is intended for the actual Frobenius coordinate quotient but does
not by itself construct Steinberg modules or prove the big-cell statement.
