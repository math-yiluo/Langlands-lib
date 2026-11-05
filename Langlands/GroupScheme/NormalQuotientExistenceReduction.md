# Unrestricted normal quotients from explicit structural inputs

`normalQuotientWithStructuralInputs` chooses an actual affine locally finite-type
quotient group and an actual projection with the prescribed full normal closed
kernel, over any field in universe `u`. It takes proofs of
`AffineCartierSmoothStatement.{u}` and `AffineHomImageStatement.{u}` as explicit
arguments. Neither structural proposition is proved in this module.

This is an internal derived assembly of the existing conditional exact-kernel
construction, unrestricted image statement, and effective affine quotient
descent. It does not claim the unconditional
`NormalSubgroupQuotientExistenceStatement.{u}`.

`AlgClosedNormalQuotientExistenceStatement` is the exact unrestricted quotient
assertion restricted to algebraically closed fields. It places no smoothness or
reducedness premise on either group. The theorem
`normalQuotientExistence_of_algClosed_quotients` proves that this specialization
implies the original arbitrary-field statement. It base changes the original
group, subgroup and inclusion to the algebraic closure in the same universe.
Affineness, local finite type, closedness and full subgroup-functor normality
persist under base change. The supplied algebraically closed-field quotient is
affine, and its projection is quasi-compact because source and target are affine.
The existing `Descent.exists_affine_fppfQuotient` descends the quotient group and
its original projection through the affine fpqc field cover. It retains the
original subgroup as the exact kernel on every relative scheme test.

The descended target is locally of finite type by
`locallyOfFiniteType_target_of_fppfQuotient`. A locally finite-type morphism to
the spectrum of a field is locally of finite presentation because the base is
noetherian. The composite of the projection with the quotient structure map is
the original structure map. Local finite presentation therefore descends along
the flat, surjective, locally finitely presented projection, by the existing
source-descent theorem. This yields local finite type of the quotient without
assuming smoothness or reducedness.

Over an algebraically closed field,
`algClosed_normalQuotientExistence_with_structural_inputs` uses
`normalKernelRepresentationWithCartier` to obtain a finite matrix
representation with precisely the prescribed full kernel. The supplied
unrestricted image proposition factors that representation through an actual
affine locally finite-type group and an fppf projection. Its kernel equality is
rewritten using the exact representation-kernel equality. The general linear
target is smooth and hence locally of finite type; no smoothness of the source
is inferred or required.

`normalQuotientExistence_with_structural_inputs` combines this construction with
the arbitrary-field descent reduction. Its conclusion is exactly the published
universe-general quotient proposition, still conditional on the two structural
inputs. Classical choice in `normalQuotientWithStructuralInputs` selects the
actual quotient and projection, retaining affineness, local finite type, and the
full `IsFppfQuotient` predicate as proofs in the resulting subtype. The original
target statement and its imports are unchanged.
