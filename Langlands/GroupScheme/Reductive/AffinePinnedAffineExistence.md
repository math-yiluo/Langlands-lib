# Inverse simple-root torus values over affine coefficient bases

This internal construction is a coefficient-ring specialization of the published
`AffinePinnedModel.exists_fppf_simpleRoot_values`. It forms part of the local
existence argument for relative pinned comparisons and introduces no additional
literature assertion.

For any affine pinned model `N`, any commutative `N.ring`-algebra `A`, and any
tuple `c` of units indexed by the simple roots of `N`, the theorem
`exists_fppf_inverse_simpleRoot_values` supplies a scheme `W`, a morphism
`p : W → Spec A` that is flat, surjective and locally of finite presentation,
and a point of the split coordinate torus over `W`. On every compatible test
`Spec B → W` for any commutative `A`-algebra `B`, the monomial of the simple root
`s` has value the image of `(c s)⁻¹` in `Bˣ`. Neither `W` nor the test rings are
assumed connected, and `W` need not be affine.

The definition `AffineInverseSimpleRootValuesStatement` states precisely this
universal assertion. The theorem `affineInverseSimpleRootValuesStatement` proves
it in every universe.

The proof first uses `affineUnitSectionsEquiv` to view each inverse coefficient
unit as a global unit on `Spec A`. It applies the existing simple-root lifting
theorem to the scalar extension of `N`, using the identity coordinate
isomorphism. The resulting map to the identity object of `Over (Spec A)` has
underlying morphism equal to the structure map of the cover, so its geometric
properties give the three asserted properties of `p`.

On a compatible affine test, the actual-character equation of the lift becomes
the simple-root coordinate monomial by
`splitTorus.pointsEquiv_exponentCharacterOnTorus`.
The lemma `affineUnitSectionsEquiv_restrict`, proved using
`Scheme.ΓSpecIso_naturality`, identifies restriction of global units with the
specified coefficient algebra map. Applying the multiplicative equivalence to
the character equation and distributing it over products and integer powers
gives the claimed coefficient equation. The affine section point used here is
the actual test evaluation from `AffinePinnedAffineCorrection`.
