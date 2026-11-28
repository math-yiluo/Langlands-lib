# Cyclotomic splitting for units–lattice coefficients

`numberFieldUnitsLatticeCyclotomicSplitting` proves
`NumberFieldUnitsLatticeCyclotomicSplittingStatement`. For the separable
closure \(\Omega\) of a number field \(K\) and a smooth finite free lattice
\(X\), write \(A=\Omega^\times\otimes_{\mathbb Z}X\). The proof uses the
Kummer sequence at finite cyclotomic layers and the uniform annihilator below.
The Kummer argument is related to Platonov–Rapinchuk, *Algebraic Groups and
Number Theory*, §6.5, Lemma 6.20 (printed p. 341).

## Uniform annihilator

The kernel of the action on a smooth finite free lattice is open because it
is the intersection of the stabilizers of a finite basis. On an open subgroup
in this kernel, the basis writes the units–lattice coefficients as a finite
product of units representations. Hilbert 90 supplies a coboundary in each
coordinate. For any open subgroup, restriction to its intersection with
the kernel followed by corestriction multiplies a degree-one class by the
relative index. The relative index divides the index of the kernel, yielding
one positive annihilator \(d\) valid on all open subgroups.

## Splitting a prime-power class

For a class \(x\) killed by \(\ell^a\), where \(\ell\) is prime, write
\(d=nd'\) with \(n=\ell^{v_\ell(d)}\) and \(\ell\nmid d'\).
Tensor the Kummer sequence with \(X\) to obtain
\[
0\longrightarrow \mu_n\otimes_{\mathbb Z}X
\longrightarrow A\xrightarrow{\,n\,}A\longrightarrow 0.
\]
The free lattice is flat, so tensoring preserves exactness. The kernel
is finite by the finite basis description, and it is killed by \(n\)
since it injects into the kernel of multiplication by \(n\) on \(A\).
Apply `numberFieldFiniteModuleCyclotomicKilling` to the image of \(x\)
under the connecting map in degree one. Its restriction vanishes over
a layer \(D=K(\mu_{\ell^r})\).

The connecting map commutes with restriction, so exactness gives
\(x|_D=n y\) in degree one. The layer is finite and its fixing subgroup
is open, so \(d y=0\) by the uniform annihilator. Thus \(d' x|_D=0\)
and \(\ell^a x|_D=0\). Coprimality gives \(x|_D=0\), and restriction
preserves this vanishing over every intermediate field containing \(D\).

## Combining the layers

Induct on the annihilator \(m\) using prime powers and coprime products.
For \(m=1\) the class is zero and the level is \(1\). If \(m=ab\) with
\(a,b\) coprime, apply the two induction hypotheses to \(b x\) and \(a x\),
respectively. The layer at the product of the two levels contains both
layers. There \(x\) is killed by both \(a\) and \(b\), hence vanishes.
The prime divisors of the product of the levels divide \(m\).

A field containing a primitive root of order \(N\) contains all roots
of that order's power equation \(t^N=1\), hence contains the chosen
layer. In the locally constant cochain complex a class in degree one
is zero exactly when its cocycle is a coboundary. Applying this
description to the restricted cocycle gives the pointwise witness in
the statement.
