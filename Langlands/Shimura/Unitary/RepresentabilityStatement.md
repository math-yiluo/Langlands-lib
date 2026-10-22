# Affine representability of the rational similitude functor

Author: Worker 57. This is an exact proposition target, not a proof or a
choice of a canonical model.

`SimilitudeRepresentabilityStatement` quantifies a ring `A` in any carrier
universe `u`, a rational algebra structure, finite dimensionality over the
rationals, and an actual rational-linear algebra anti-involution. It concludes
the existence of a commutative rational algebra `B`, finitely presented over
the rationals, together with a natural isomorphism

`Hom_Q-alg(B, S) ≅ similitudes(S tensor_Q A)`

for all commutative rational test algebras `S` in the same universe. The
right side is the published `AlgebraInvolution.similitudeFunctor`, followed
by the forgetful functor from groups to types. It uses actual invertible
algebra elements and invertible scalar multipliers with the proved
similitude equation; it is not a replacement functor defined by the target.
Naturality is required for every rational algebra homomorphism of test
algebras. The test-algebra universe is `u`, so the result does not silently
restrict the input algebra to Type 0.

Neither `B` nor the representing isomorphism is an input. Once this target
is proved, the spectrum of `B` and its structure morphism to `Spec Q` give
an actual affine realization. Transfer of the existing pointwise group
law to a group-scheme structure is a further explicit Yoneda construction;
this target does not replace it with an unspecified output scheme. No
constructor choosing `B` is defined before a proof of the target.

The theorem is a derived prerequisite of Kottwitz (1992), Section 1,
printed page 654 (PDF page 2), where the rational algebraic group is given
through its points on every commutative rational algebra. It isolates the
representability needed to interpret that functor as an affine group.
Harris (1999), Section 1, printed page 301 (PDF page 3), gives the
second-kind unitary algebra input and rational similitude equation.
Both original passages were read, including visual inspection. The target
is stated for arbitrary finite-dimensional rational algebras with involution;
this elementary finite-equation generalization does not assert reductivity
for arbitrary such algebras. Harris's central-simple case is included after
rational finite dimensionality is obtained from the number-field tower.

Source IDs and fingerprints:

- `kottwitz-1992-lambda-adic-simple-shimura`, *On the lambda-adic
  representations associated to some simple Shimura varieties*,
  Invent. Math. 108 (1992), pp.653-665;
  SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
  *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), pp.299-318;
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies are the published `Langlands.Shimura.Unitary.Similitude`
and `Involution` modules and the actual Mathlib `CommAlgCat`, `coyoneda`,
and `Algebra.FinitePresentation` interfaces at commit
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
The target requires independent acceptance and publication, followed by
a separately assigned proof of this entire Library declaration. It is
not a proof of representability, a PEL moduli construction, or a completed
Shimura canonical model.
