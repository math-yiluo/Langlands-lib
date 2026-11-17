# Algebraic flatness of full affinoid-domain restrictions

Author: Worker 310.

`PresentedAffinoidAlgebra.Domain.FlatnessStatement` states that, for every
complete ultrametric normed field `K : Type u`, every presented affinoid
algebra `A` over `K`, and every `U : Domain K A`, the actual bounded
structural map `U.baseMap : A → U.algebra` is algebraically flat.
The conclusion is Mathlib's `RingHom.Flat` for
`U.baseMap.toAlgHom.toRingHom`, including its specified scalar action.

The algebras retain their finite presentations with arbitrary positive real
polyradii and closed defining ideals. The statement permits trivial
valuations and zero quotient algebras. `U` has the existing full
affinoid-test universal property `Represents`; flatness is a conclusion,
with no additional condition on its represented closed locus.

## Source correspondence

The source is V. G. Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Definition 2.2.1, printed p. 27 / PDF p. 41, defines an affinoid domain
through bounded maps and their universal factorization property.
Proposition 2.2.4(ii), printed pp. 29–30 / PDF pp. 43–44, asserts flatness
of its affinoid algebra over the ambient affinoid algebra. Its general
case includes arbitrary ground-field valuation and general affinoid radii.

The existing `Domain` additionally stores the actual structural map's
spectral image equality, so each input supplies the source's domain data.
This statement specializes that source result to the Library's actual
finite positive-polyradius quotient presentations. It asserts the
algebraic flatness conclusion only; it introduces no analytic stalk
comparison or finite-cover descent theorem.

## Purpose and status

This is a statement, with no proof supplied here. It isolates a substantial
algebraic prerequisite for transporting the pointwise flat and unramified
condition on finite affinoid maps through recognized domain restrictions.
Local faithful flatness and reflection of pointwise properties require
separate proofs from this flatness conclusion.
