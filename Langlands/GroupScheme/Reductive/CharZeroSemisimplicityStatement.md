# Complete reducibility for reductive groups in characteristic zero

`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement` states the
complete-reducibility prerequisite for the characteristic-zero branch of Haboush's
theorem. It quantifies over every field `k : Type u` with `Field k`, `IsAlgClosed k`
and `CharZero k`, every group scheme `G` over `Spec k` with the unchanged Library
predicate `IsPseudoReductive G`, and every finite coordinate representation
`ρ : MatrixRepresentation G n`. Over an algebraically closed field this group
hypothesis means connected reductive. The field universe `u` is arbitrary, and
coordinate types are finite types in `Type`, as in the existing Haboush statement.

The conclusion is Mathlib's `Representation.IsSemisimpleRepresentation` for the
actual representation `ρ.rationalRepresentation` of the group of scheme-valued
`k`-points. This means that every invariant linear subspace has an invariant
complement; it is the semisimplicity of this particular rational representation,
not a claim about arbitrary abstract representations of the rational-point group.
No complete-reducibility proof is supplied in this statement unit.

The accompanying theorem
`invariant_polynomial_of_reductive_charZero_semisimplicity` is a conditional
consumer. It assumes the displayed proposition explicitly, uses the smoothness
field of `IsPseudoReductive`, and invokes the implemented degree-one separation
construction. Choosing degree one yields exactly the polynomial conclusion of the
existing `ReductiveGeometricReductivityStatement` for characteristic-zero fields.
The invariance still quantifies over every test scheme and all its section-valued
coordinate vectors, including nonaffine and nonreduced tests. No restriction to
rational-point polynomial invariance occurs. The premise is not an established
theorem, and this conditional theorem does not prove the existing Haboush target.

Provenance: Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third enlarged
edition (1994), Appendix to Chapter 1, Section A, printed p.191 (PDF zero-based page
index 202), definition (ii) of linear reductivity and the following equivalence of
(i) and (ii) in characteristic zero. Source ID
`mumford-fogarty-kirwan-1994-git-3rd`. The predicate is the source's complete
reducibility conclusion expressed in the Library's actual coordinates and Mathlib
semisimplicity. The conditional consumer is derived from
`MatrixRepresentation.exists_invariant_polynomial_of_rational_semisimple` and is
included to identify its exact use and its retained proof obligation.
