# Weil-quotient extensions with vector-bundle series kernels

This internal specialization combines `VectorBundleSeriesCocycle` with
`WeilSolvableCocycle`. It works over `Spec A`, in every universe `u`, for
an arbitrary commutative coefficient ring `A` and a supplied finite
projective commutative `A`-algebra `B`.

The data consist of group homomorphisms `j : K ⟶ H` and `q : H ⟶ T`.
The underlying map of `j` in schemes over `Spec A` is monic, and its
all-test image equals the image of the represented kernel of `q`. The
schemes `H` and `T` are affine, and `q` is flat, surjective and locally of
finite presentation. The kernel group `K` is affine over `Spec A` and
comes with a finite actual vector-bundle normal series. Finally, an
actual group-scheme isomorphism `T ≅ WeilGm.groupScheme A B` is supplied.
Neither an abstract torus predicate nor geometric unipotence alone is
substituted for these data.

Under `Subsingleton (CommRing.Pic B)`, every `H`-valued cocycle on an
arbitrary single fppf cover `U` of `Spec A` is trivial. The cover's total
space need not be affine or quasi-compact. The proof applies finite
vector-bundle series cocycle vanishing to `K`; on `Spec A` the generic
vanishing predicate is definitionally the predicate required by the
existing Weil-quotient extension theorem. That theorem supplies a scheme
section of `q`, trivializes the quotient cocycle by Picard vanishing,
lifts its primitive through the section, and twists into the kernel.
Kernel vanishing and untwisting give a primitive for the original cocycle.

`vectorBundleWeilExtensionFppfPicardCochain` chooses this original-cover
morphism `f : U ⟶ H.X`. Its specification gives
`ξ(a,b) = (a ≫ f) * (b ≫ f)⁻¹` on every scheme test over `Spec A`.
The two further vanishing theorems obtain coefficient Picard triviality
from `FiniteAlgebrasHaveTrivialPicard A` or from
`Finite (MaximalSpectrum A)`, respectively. All extension, series and
presentation hypotheses remain in these specializations.

These are internal deductions from the cited Lean modules and their
existing Picard and semi-local consequences. The module does not construct
a Borel quotient, its unipotent filtration, or its torus's Weil-restriction
presentation. It does not prove quasi-split inner-form existence or the
unconditional reductive semi-local inner-form theorem.
