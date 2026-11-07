# Principal neighborhoods of integral fibres

This internal development derives the affine principal-neighborhood step for
the global integral scheme pushout from the unit witness in
`Langlands.Algebra.IntegralAlgebraPrimeAvoidance`.

`exists_basicOpen_of_integral_field_algebra` considers any ring map `R → A`
where `A` is integral over a field, and any open subset of `Spec R` containing
the image of `Spec A`. It produces a principal open containing that entire
image and contained in the prescribed open. The proof takes the vanishing ideal
of the closed complement. Its image in `A` is the unit ideal, since otherwise a
prime containing it would map into both the given open and its complement.
The algebraic unit witness supplies a member of the vanishing ideal which is
a unit in `A`. Its principal open has both required containments.

This proof uses arbitrary commutative rings and imposes no finite generation
hypothesis on the integral field algebra.

`exists_basicOpen_of_integral_field_scheme` transports this assertion to an
actual morphism between affine schemes, with an integral field-algebra
structure on the source global sections. The proof uses the canonical
affine-spectrum isomorphisms and their naturality. It produces a global
section of the target whose principal open contains the entire morphism
image and lies in the specified open.

`exists_basicOpen_of_integral_field_morphism` supplies the algebra hypothesis
from an actual integral morphism `p : T → Spec k`. Its source is affine because
the target is affine and the morphism is affine. The composite
`k → Γ(Spec k, ⊤) → Γ(T, ⊤)` defines the scalar structure; integrality of the
second map and the canonical isomorphism for the first give an integral
`k`-algebra. No scalar compatibility is required of the separate morphism
`f : T → X`.

`exists_basicOpen_of_integral_fibre_in_affineOpen` applies this result to the
scheme-theoretic fibre of an integral morphism `j : Z → Y` at a point `y`.
Its inputs are an affine open `U` of `Z` containing every point of that fibre
and an arbitrary open `W` containing the same points. The fibre map to
`Spec κ(y)` is integral by base change. The fibre inclusion lifts through
`U.toScheme`, so the preceding lemma gives a global section there. The
isomorphism `U.topIso` transports this section to `Γ(Z, U)`, and the image
formula for principal opens gives precisely the two required containments
in `Z`. The fibre homeomorphism converts every point with `j z = y` into a
point of the scheme-theoretic fibre.

`integralFibrePrincipalNeighborhood` chooses the resulting section together
with proofs that its principal open contains the entire fibre and lies in
`W`. Fibres may be infinite or empty; neither the integral algebra nor the
morphism is assumed finite.

The ambient-section transport was adapted from Worker 1770's shared
`exists_basicOpen_of_finite_in_affineOpen` draft; here integral-field
prime avoidance replaces finite-point avoidance. The development constructs
principal neighborhoods only. Compatible affine neighborhoods and the global
scheme pushout remain separate obligations.
