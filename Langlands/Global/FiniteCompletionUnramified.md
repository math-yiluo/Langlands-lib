# The completed unramified extension at a finite place

`CompletedUnramified` specializes the normed completion of the inertia fixed field to the actual number field completion at a finite place. Its valuation comparison uses the existing valuative relation and topology of the completion. It is a complete ultrametric normed field, with a local base embedding and a global base embedding obtained by composition. `unramifiedBaseNormedField` specifies the norm whose spectral extension defines the completion. This norm induces the given finite-place topology. The local embedding is isometric for this norm and supplies `completedUnramifiedNormedAlgebra`.

The Krull Galois group of the unramified algebraic extension acts on the completed field through the canonical isometric extensions of its algebraic automorphisms. `completedUnramifiedArithmeticFrobenius` is the extension of the lift acting on the residue field by the residue-cardinality power map.

This realizes the completed local base associated with Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999), §4, (4.3), p. 309. The maximal unramified extension and Frobenius used on the local side are also described in Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p* (1998), Appendix, p. 208, before (A.9).
