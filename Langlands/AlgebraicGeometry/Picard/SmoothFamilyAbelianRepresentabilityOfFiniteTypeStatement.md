# Statement: reducing the smooth-family representer to finite type over `ℤ`

`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfFiniteTypeStatement.{u}`
is the implication

`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} →
SmoothFamilyAbelianRepresentabilityStatement.{u}`

between two published propositions, both used unchanged:

- the hypothesis `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`
  (module `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`) says
  the following. Let `R : Type u` be a commutative ring of finite type over
  `ℤ` and `A` an abelian scheme over `Spec R`. Then there is an abelian
  scheme `B` over `Spec R` and a rigidified family `L` for `A` on `B.X` with
  `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`;
- the conclusion `SmoothFamilyAbelianRepresentabilityStatement.{u}`
  (module `SmoothFamilyAbelianRepresentabilityStatement`) says the same for
  every scheme `S : Scheme.{u}` with `QuasiSeparatedSpace S` and every
  abelian scheme `A` over `S`, giving `B : AbelianScheme S` and a rigidified
  family `L` for `A` on `B.X`.

In both propositions the predicate
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` is the existing one. It
requires that `L` is smooth-family algebraically trivial, and that each such
rigidified class on each quasi-separated test `T` over the base is obtained
by pulling back `L` along exactly one morphism `T ⟶ B.X` over the base.
Nonreduced tests are included. The statement adds no hypothesis beyond the
finite-type case. In particular it assumes no noetherianity, projectivity,
polarization, ordinary-Picard existence or comparison result, and all
schemes lie in universe `u`.

## Provenance

This is an internal derived interface, not a literal statement of the
source. It follows the reduction steps in the proof of Raynaud's theorem in
Faltings–Chai, *Degeneration of Abelian Varieties* (1990), Chapter I. The
theorem is Theorem 1.9 on printed p. 5 (PDF p. 17), and the reduction steps
are on printed p. 6 (PDF p. 18). Step (1) reduces to an affine base
`S = Spec(R)`. Step (2) writes `R` as the union of its subalgebras `Rᵢ` of
finite type over `ℤ` and, since `A` is of finite presentation over `S`,
reduces to the case where `R` is of finite type over `ℤ`. The source applies
these steps to the schemeness of `A` and of `Pic(A/S)`. Here the same pattern
is applied to the existence of an abelian-scheme parameter carrying a
universal rigidified smooth-family class. The statement carries only this
reduction. The existence argument over bases of finite type over `ℤ` stays
the separate hypothesis `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`.
Its proof is a separate task.

The intended proof uses only published Library results: Zariski gluing of
representers along an open cover of a quasi-separated base, spreading an
abelian scheme over `Spec R` to a finitely generated subring of `R`,
universal base change of smooth-family representers, and transport of a
universal family along an isomorphism of abelian schemes.
The interface was designed by Worker 930 with Worker 141, within task
`e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`.
