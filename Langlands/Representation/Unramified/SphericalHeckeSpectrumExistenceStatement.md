# Existence of a standard spherical Hecke spectrum

`Langlands.Unramified.SphericalHeckeSpectrumExistenceStatement` is an unproved
proposition-valued definition. It states that every actual irreducible
admissible smooth spherical representation of `GL_(r+1)(F)` has a multiset
`s : Eigenvalues (r+1)` satisfying the existing
`HasSphericalHeckeSpectrum F A s` relation.

The field is every `F : PadicField.{uF} p` with `[Fact p.Prime]`, and `r` is any
natural number, including zero. The representation carrier universe `uV` is
independent of `uF`. All field and group topologies, the spherical subgroup
`GL_(r+1)(O_F)`, complex coefficients, and Hecke operators are the actual
constructions imported from `HeckeOperators`. The hypothesis is that the
original spherical fixed submodule is nonzero; no replacement carrier or
choice of spherical vector is supplied.

Writing `n = r+1`, `q` for the residue cardinality and `T_i` for the indicator
of the double coset of `diag(ϖ,...,ϖ,1,...,1)` with `i` uniformizers, the
conclusion says that on every vector in that fixed submodule, for every
`0 ≤ i ≤ n`, the integrated operator `T_i` acts by

`(sqrt(q))^(i*(n-i)) * (-1)^i * coeff_i (∏_{z in s} (1-zX))`.

The Haar measure gives the spherical subgroup mass one. `sqrt(q)` is the
positive real square root, mapped to the usual complex field. Every member of
the multiset is a complex unit, and all multiplicities are retained. The
index-zero assertion is the identity normalization already proved by
`standardHeckeOperator_zero_scalar`.

## Provenance and intended dependency boundary

This statement is a derived specialization of Gross, *On the Satake
isomorphism* (1998), section 6, retained PDF pages 11–12. Equations (6.2)–(6.3)
identify the character on the spherical line, and Proposition 6.4 assigns
its semisimple dual-group conjugacy class. For `GL_n` this is a class of
invertible complex matrices. Equations (6.5)–(6.7), especially (6.7), express
the Euler polynomial using precisely the normalized scalars of the standard
double-coset elements. Taking its multiset of eigenvalues gives the statement
above. The full multiset and the independent carrier universe are explicit
formalization choices consistent with that representation-invariant claim.

The registered source is `gross-1998-satake-isomorphism`, retained
`Gross--On the Satake isomorphism--1998.pdf`, SHA-256
`9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`.

A proof may avoid using a Satake classification theorem: the published
fixed-line theorem makes each standard operator scalar; the last standard
element, the central uniformizer double coset, is invertible, so its scalar
is nonzero. The normalized signed scalars then define a degree-`n` complex
polynomial with constant coefficient one. Factoring it over the complex
numbers expresses it as `∏(1-zX)` with exactly `n` nonzero values, counted
with multiplicity. This describes a possible proof route, not implemented
proofs in this module.

This proposition does not assert `HasSphericalSpectrum`, a principal-series
subquotient realization, uniqueness of the spectrum, or equivalence of
representations with the same Hecke scalars. Those are separate obligations.
In particular, its future proof must not use the converse of the full
principal-series/Hecke comparison if that converse depends on spherical
exhaustion. The present statement supplies no proof of
`SphericalSpectrumExistenceStatement`.
