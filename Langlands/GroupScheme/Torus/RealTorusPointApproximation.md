# Simultaneous approximation of real torus points modulo norms

For a torus \(T\) over a number field \(F\), let \(K_w\) be the completion at
a real place, let \(M_w\) be its algebraic closure, and let \(T_w\) be the
base change of \(T\) to \(K_w\). Given a family \(p_w \in T_w(K_w)\),
`RealTorusPointApproximationStatement` gives \(z \in T(F)\) and, for each
\(w\), an \(r_w \in T_w(M_w)\) such that
\[
  p_w = z_w\,\operatorname{Nm}_{M_w/K_w}(r_w).
\]
Here \(z_w\) is coefficient extension followed by the affine point
equivalence for the base change. The norm is the finite Galois point norm
on \(T_w\). The extension \(M_w/K_w\) has degree two.

Fix a finite Galois splitting field \(E/F\) and choose an embedding of \(E\)
in each \(M_w\). At a chosen place \(w\), the real norm representative
gives an invariant cocharacter whose value at \(-1\) has the class of
\(p_w\). The tower comparison identifies this with the value of a
cocharacter over an intermediate field \(N\) of \(E/F\). The chosen
embedding of \(N\) in \(M_w\) factors through \(K_w\).

Choose a unit of \(N\) whose sign is negative at that embedding into
\(K_w\) and positive at all other embeddings into real completions of
\(F\). Evaluate the intermediate cocharacter at this unit and take its
point norm from \(N\) to \(F\). Modulo norms at a real place, the
intermediate norm formula keeps only the factors at embeddings fixed
pointwise by local conjugation. These embeddings factor through the local
real field. Each positive factor has trivial class. At \(w\), the sole
negative factor comes from the inclusion of \(N\) in \(E\) and has the
class of \(p_w\).

The product of these global points over the finite set of real places
meets all the prescribed classes. The equality of classes gives a product
with a conjugate over \(M_w\). Naturality of the affine point equivalence
identifies this product with the extended norm on \(T_w\). Injectivity of
extension of affine points yields the asserted equality over \(K_w\).

This is an internal lemma for torus cohomology localization. It supplies
approximation modulo local norms on the quotient torus in the approach
using an induced torus resolution. Platonov and Rapinchuk use approximation
on a quotient torus in the proof of §7.3, Corollary 2, *Algebraic Groups and
Number Theory* (1994), pp. 418–419.
