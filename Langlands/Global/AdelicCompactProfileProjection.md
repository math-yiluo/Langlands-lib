# Right compact coefficient functions for averaged convolution

`Langlands.Global.AdelicGroupPoints.HasAdelicCompactProfiles`
requires \(k\mapsto f(xk)\) to belong to a fixed subspace \(E\) of
functions on the infinite compact subgroup, for every adelic \(x\).
For a continuous compact-finite function, the proof uses the span of
these coefficient functions as \(E\). Expanding the right orbit in a
finite basis proves finite dimensionality, and left translation of a
coefficient function corresponds to changing \(x\).

In a finite-dimensional, left-translation-invariant subspace of
continuous coefficient functions, the Haar inner product gives a
reproducing vector at the identity. Left translating it gives the
reproducing vectors at other points. Their Hermitian symmetry implies
that averaging any continuous function with the first weight gives
coefficients in \(E\). This uses the closure of a finite-dimensional
space of functions under pointwise integration of an integrable family
in that space. The weight reproduces every function already satisfying
the coefficient condition, and its inverse supplies a weight for
averaging over inverse translates. Both weights have finite left
translate spans.

The Iwasawa height power is a nonzero scalar on each right compact
coset. Twisting therefore preserves the prescribed coefficient
condition, and left averaging a test kernel gives the same condition
on the output of convolution transported through the twist.

The finite coefficient space and its reproducing weights implement
the use of a finite set of compact types and its two-sided kernel
averaging in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series*, I.4.5, printed pp. 60–61
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).

`rightCompactFunctionAverage` integrates an arbitrary function along its right compact translates against a continuous weight.
