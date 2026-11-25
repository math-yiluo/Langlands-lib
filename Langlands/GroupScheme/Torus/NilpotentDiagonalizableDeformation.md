# Nilpotent deformations of diagonalizable groups and Hom lifting

Let `R` be a commutative ring, `J` a nilpotent ideal, and `G` a flat affine
group over `Spec R`. If its actual reduction over `R/J` is diagonalizable,
then `G` is diagonalizable. This conclusion requires no local-ring,
noetherianity, completeness, or finite-type assumption on the base or group
beyond the finite generation built into the diagonalizable predicate. The
character group may have torsion.

`nilpotentCoordinatePresentation G J hJ hG` constructs an actual bialgebra
presentation of `O(G)` as `R[N]` with `N` finitely generated abelian. Extract
the actual reduced presentation `(R/J) ⊗ O(G) ≃ (R/J)[N]` using
`diagonalizableReductionPresentation`. Flatness of the group makes its
chosen coordinate Hopf algebra flat by the
`Diagonalizable.flat_hopfAlgebra` theorem. The pure theorem
`exists_bialgEquiv_of_baseChange` then lifts the reduced presentation to an
actual bialgebra equivalence `O(G) ≃ R[N]`. The definition keeps the same
character group `N` and its finite-generation instance.

`isDiagonalizable_of_nilpotent_reduction` reconstructs the actual
isomorphism of group schemes from this coordinate equivalence and compares
the affine diagonalizable model with the relative one. The proof route and
lifting argument are documented in the included
`CompleteLocalDeformation/Lifting.md`; the pure theorem uses convolution
idempotent lifting and flat module arguments.

Now suppose that `R` is local and that `H` is already diagonalizable over
`R`. The nilpotent ideal `J` is proper, since a local ring is nonzero and the
unit ideal cannot be nilpotent. Thus `R/J` is a nonzero local ring.
`nilpotent_baseChange_hom_bijective` first proves `G` diagonalizable by the
preceding construction, then applies the actual diagonalizable Hom
comparison between the two local rings. It proves that the actual
base-change map
`Hom_R(H,G) → Hom_(R/J)(H_(R/J),G_(R/J))` is bijective.
`nilpotentHomBaseChangeEquiv` packages this map as an equivalence.

`specialFibre_hom_bijective_of_maximalIdeal_isNilpotent` specializes the
result to `J = maximalIdeal R`. Consequently homomorphisms lift uniquely
from the special fibre whenever the local base has nilpotent maximal ideal,
the source is diagonalizable, and the flat affine target has diagonalizable
special fibre. An arbitrary Artinian local base is an application after
establishing nilpotence of its maximal ideal.

This is internal derived content for the Artinian step in Conrad (2014),
Theorem B.3.2(2), p.289. The result supplies the actual nilpotent deformation
and local Hom-lifting step; it does not algebraize an infinite compatible
system or descend a lift along a finite étale cover, and therefore does not
by itself prove the full complete-local statement.
