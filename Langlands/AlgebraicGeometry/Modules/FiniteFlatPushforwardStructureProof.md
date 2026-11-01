# Actual structure-module pushforward: proof route

The proof derives a global presentation cover from affine-local
quasi-coherence, using the tilde presentation on a spectrum, restriction
along the affine chart isomorphism, and the equivalence with module
sheaves on the over site. The published affine-local pushforward theorem
then proves quasi-coherence of `f_* O_X`.

Finite and flat affine sections are exactly the module-theoretic
conditions on `f.app U` in the definitions of finite and flat morphisms.
For an integral target and a nonempty affine open, its function ring is
a domain. The spectrum of the affine section map gives a pullback square
with the original morphism. Native rank is invariant under this pullback;
its value on the spectrum is rank at the corresponding prime, which equals
the module rank over the domain. The module is the actual sections of
`f_* O_X` with the actual scalar action from `f.app U`.

This is an internal derivation from the published constructions and
Mathlib ring and scheme results, without a numerical rank certificate.
