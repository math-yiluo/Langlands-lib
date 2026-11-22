# Heights of actual products and Cartier duals

Over `Spec R`, the finite locally free levels are affine. Their global
sections recover the chosen Hopf coordinates via the actual affine
comparison. `productSectionsEquiv` identifies the global sections
of a product of affine commutative group schemes over `Spec R` with
the tensor product of their global sections over `R`. At each prime
of `R`, the ranks of the finite flat modules multiply, so the constant
heights of two towers add.

At each level of the Cartier dual tower, the spectrum has the
underlying finite projective dual coordinate module. The two finite
projective modules have equal rank at every base prime, so Cartier
duality preserves height. `HasHeight.dual` and `HasHeight.splitWithDual`
take a proof `hExact` of `FiniteCartierDualExactnessStatement` to form
the dual tower from the finite dual schemes. If `G.HasHeight h`, then
`HasHeight.splitWithDual` gives height \(2h\) for
`G.splitWithDual hExact`.

Tate (1967), §2.3, printed p. 166 (PDF p. 5), describes the dual tower
and its equal height. Rapoport–Zink (1996), §6.43, printed p. 309
(PDF p. 321), identifies the actual polarized split product. The
height formula here is derived from the ranks of the two coordinate
algebras on each finite level.
