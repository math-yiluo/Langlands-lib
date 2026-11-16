# Top coherent Euler coefficients under line-bundle twists

This internal module defines `TopEulerCoefficientTwistInvariant` as equality of the coefficient at a common support bound before and after tensoring the coefficient sheaf by an actual line bundle. The equality concerns the canonical coherent Euler polynomials of actual cohomology. It assumes no positive form or intersection pairing.

The proof uses Noetherian induction on a closed support. An affine open meeting an irreducible component is chosen where the tensor line bundle is trivial. The image of the coefficient sheaf in the pushforward of its restriction is supported on that irreducible component; its kernel has support in a smaller closed set. The existing coherent graph comparison makes the line-bundle twist of the image invisible to the top forward difference, while induction handles the kernel. Tensoring the short exact sequence by the line bundle preserves exactness, so additivity combines the two comparisons.

The resulting top forward differences agree whenever the coefficient sheaf has support dimension strictly below `d + 1`. The canonical Newton coefficient formula then gives equality of coefficient `d` in truncation `d`. This includes `d = 0`. The scheme is Noetherian and separated, with a proper structure map to an arbitrary field in universe `u`; the coefficient sheaf is quasicoherent with finite affine sections. Neither line bundle needs to be ample.

All results are derived from the Library's actual coherent graph, support, tensor exactness, Euler additivity and Newton polynomial results. No additional literature theorem is asserted.
