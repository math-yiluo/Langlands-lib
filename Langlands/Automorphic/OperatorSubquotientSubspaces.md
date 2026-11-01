# Invariant subspaces of actual operator quotients

This internal derived construction concerns the existing actual
`OperatorSubquotient` over an arbitrary number field universe, every natural
matrix rank and complex coefficients. It adds no CM-field or character
hypothesis.

`subrepresentationPreimage` takes the linear preimage of an invariant quotient
subspace under the actual canonical projection. `subrepresentationImage`
takes the linear image of an invariant numerator subspace under that
projection. The published projection covariance proves invariance under every
concrete operator in both constructions. Their membership formulas describe,
respectively, membership of the projected vector and existence of a numerator
representative in the specified subspace. For image invariance, the proof sends
an image witness `f` to the explicit witness obtained by applying the numerator
operator to `f`, and uses projection covariance to identify its projection.

Every preimage contains `Q.lower`, by the actual kernel of the quotient
projection. The image of a preimage is the original quotient subspace.
The preimage of an image is the original numerator subspace when that subspace
contains `Q.lower`. These inverse identities reuse Mathlib's
`Submodule.comapMkQRelIso` for the underlying module quotient.

`quotientSubrepresentationOrderIso` bundles this correspondence as an order
isomorphism from all invariant subspaces of `Q.representation` to
`Set.Ici Q.lower`, the numerator invariant subspaces containing the actual
denominator. Its forward map is preimage and its inverse is image. The
application formulas identify these maps exactly, and
`subrepresentationPreimage_le_iff` states that preimage preserves and reflects
inclusion.

The preimages of zero and the full quotient are the actual denominator and
the full numerator. The images of the denominator and the full numerator are
zero and the full quotient. These endpoint laws reuse the kernel, image and
surjectivity properties of the actual module quotient projection. The full-image
law follows from the full-preimage law and the image-of-preimage identity.

`isIrreducible_iff_isCoatom` characterizes whole-operator irreducibility of the
actual quotient by maximal properness of its denominator among the numerator's
whole-operator invariant subspaces. The proof transports simplicity of the
invariant-subspace order through the constructed order isomorphism and uses
Mathlib's `Set.isSimpleOrder_Ici_iff_isCoatom`. Mathlib's simple-order predicate
includes nontriviality, and a coatom is proper, so the zero quotient is excluded.

Provenance is internal. The module specializes the standard module quotient
correspondence to the published actual automorphic quotient, with intrinsic
whole-operator covariance. Mathlib supplies the module image/preimage inverse
proofs and the order-theoretic maximality criterion. The published
`LengthCriterionProof.push/pull` and `IntervalLiftProof` supply related maps for
successive quotient filtrations; this unit instead bundles the correspondence
for every invariant subspace of a fixed actual automorphic presentation. It
does not assume a maximal denominator or an irreducible constituent exists,
and asserts no spectral existence, quotient topology or function evaluation.
