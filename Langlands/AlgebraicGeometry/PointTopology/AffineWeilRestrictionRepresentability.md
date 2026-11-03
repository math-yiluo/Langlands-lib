# Affine tests for the actual universal comparison

Worker 105 derives the agreement between the canonical comparison defined by
the universal morphism and the existing tensor-valued affine-test point
equivalence. This is construction infrastructure for Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 2.4,
printed page 3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The coefficient algebra `B` is finite projective over an arbitrary commutative
ring `A`, and `X` is an actual affine scheme of finite type over `Spec B`.
Test algebras are arbitrary commutative `A`-algebras. No topology, finite
presentation, Noetherianity or faithfulness is assumed. This unit constructs
the equivalence on relative spectra; extension to arbitrary test schemes
remains a separate obligation.

Coordinate points commute with maps of value algebras, by contravariance of
the fully faithful spectrum functor. Every point of a relative spectrum
is the spectrum of its algebra map. Naturality of the actual pullback's
tensor presentation therefore reduces the canonical comparison to scalar
extension of that algebra map followed by the universal point. This is exactly
the defining formula for the previously constructed representing equivalence.

More precisely, `affineWeilRestrictionComparison_affine` identifies the
canonical comparison at `Spec T` with the tensor-valued point equivalence
followed by precomposition with the canonical isomorphism
`Spec T ×_{Spec A} Spec B ≅ Spec(B ⊗[A] T)`. Its proof first recovers the
algebra map of the actual point using full faithfulness of `Spec`, then
uses naturality of this isomorphism and the universal-point coordinate
identity. Associativity assembles these equalities.

`affineWeilRestrictionAffineTestEquiv` composes that existing tensor-valued
equivalence with the Hom-set equivalence induced by the same isomorphism.
Its source is the actual morphism set from `Spec T` to the constructed
Weil-restriction scheme over `Spec A`; its target is the actual morphism set
from the scheme pullback to `X` over `Spec B`.
`affineWeilRestrictionAffineTestEquiv_apply` proves that its forward map is
exactly the canonical counit comparison. The inverse transports a morphism
along the inverse tensor-presentation isomorphism and then applies the
inverse existing point equivalence. These are intrinsic laws of this
construction, with no assumed bijectivity or representability premise.

The affine coefficient-change identity reuses
`affineSchemePointEquiv_changeRing` from
`AffineProductRingTopologyProof`, with its explicit value-ring arguments.
