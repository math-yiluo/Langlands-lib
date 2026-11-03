# Noetherian affine closed submonoids are subgroups

This internal prerequisite target isolates the closed-submonoid argument in
pointed-image generation. It follows Worker 1378's shear construction design
on the project's actual group schemes and representability-transfer interface.
It is not a transcription of a numbered literature assertion.

Work over an arbitrary scheme `B` in universe `u`. Let `G` be an actual group
scheme over `B`, and let `j : Z ⟶ G.X` be an actual closed immersion in
`Over B`. Suppose multiplication on `G`, restricted to the square of `Z`,
factors through a morphism `m : Z ⊗ Z ⟶ Z`, and the unit factors through
`e : 𝟙_ (Over B) ⟶ Z`. The displayed equations are equalities of actual
morphisms. Assume that the underlying scheme of `Z ⊗ Z` is affine and locally
Noetherian.

`NoetherianClosedSubmonoidStatement` asks for a group scheme `H`, a closed
subgroup homomorphism `i : H ⟶ G`, and an actual isomorphism `a : Z ≅ H.X`
whose composite with `i` is exactly `j`. Thus the conclusion identifies the
original closed submonoid with the underlying scheme of a closed subgroup.
This preserves its full functor on all test schemes, including nonreduced
ones. No field, smoothness, reducedness, irreducibility, or characteristic
hypothesis is imposed.

The intended proof uses the shear `(x,y) ↦ (x,xy)` on the square. Its
restriction to `Z ⊗ Z` is a closed immersion endomorphism and is invertible by
the separate Noetherian affine finiteness theorem. Applying its inverse to
`(x,1)` supplies inverse points over every test scheme. The existing
representability-transfer construction can then furnish the actual group
object and inclusion. This file defines the target only; no inverse
factorization or subgroup structure is assumed.
