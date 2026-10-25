# Neighborhoods of one in actual local norm images

Author: Worker 460.

`Langlands.Global.AdelicFunctoriality.LocalNormNeighborhoodStatement.{u,v}`
defines one proposition for arbitrary number fields `K : Type u` and
`L : Type v`, with their field and number-field instances and a given
`Algebra K L`. The universes `u` and `v` are independent. For each such
extension it asserts the conjunction of the following two statements.

- For every `p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)`, every
  `q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)`, and every witness
  `h : q.asIdeal.LiesOver p.asIdeal`, install `h` as an instance. Then
  `Set.range (Units.map (FiniteExtension.localNorm p q))` belongs to
  `𝓝 (1 : (p.adicCompletion K)ˣ)`.
- For every `p : NumberField.InfinitePlace K`, every
  `q : NumberField.InfinitePlace L`, and every witness `h : q.LiesOver p`,
  install `h` as an instance. Then
  `Set.range (Units.map (InfiniteExtension.localNorm p q))` belongs to
  `𝓝 (1 : p.Completionˣ)`.

Thus the quantifiers cover every actual pair of places above one another
and every lying-over witness. The finite primes are the actual nonzero prime
ideals of the rings of integers. The units are the full multiplicative groups
of the completed fields, rather than the units of the completed valuation
rings.

The imported [Norm](Norm.md) module exposes the local norm maps constructed
in [Extension](Extension.md). Each map is `Algebra.norm`, the determinant
norm for the actual completion embedding induced by the given global
algebra and the installed lying-over witness. The open scopes select these
published completion algebras. The target uses the existing topologies on
`p.adicCompletion K` and `p.Completion` and Mathlib's topology on their
units; it introduces no topology or algebra instances.

Membership in `𝓝 1` means that the norm image itself is a neighborhood of
one, equivalently that it contains an open set containing one. No Galois,
cyclic, ramification, norm-openness, finite-index, reciprocity, global
inequality, or approximation premise occurs. Finiteness of the global
extension follows from the number-field assumptions. A real place below
a complex place is included; the target asserts the neighborhood property
at that place without asserting surjectivity on real units.

This file defines the proposition; it does not supply a theorem inhabiting
it. The published [LocalNormNeighborhood](LocalNormNeighborhood.md) module
by Worker 269 already proves its finite and infinite assertions separately
as `range_finiteLocalNorm_mem_nhds` and
`range_infiniteLocalNorm_mem_nhds`, at independent universes. The latter
even omits the `NumberField L` assumption. The present definition gives the
combined exact target requested for a separate proof follow-up.

## Derived provenance

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea,
2009, Chapter V §4, the proof of Theorem 2, printed p.17 / PDF p.26.
Registered source: `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`,
retained at
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
The original passage and the appended errata on PDF p.202 were read;
the errata contain no correction to this passage.

Artin and Tate use approximation to make the exceptional local components
of a principally adjusted idele close enough to one to be local norms.
This definition isolates the local neighborhood fact used there. It is
derived packaging of that input for number fields, not a statement of the
full global theorem. It explicitly includes every infinite place, which
is needed when the exceptional set is presented using finite primes.
It does not assert weak approximation, existence of a principal adjustment,
or assembly of an upper idele.

The source passage uses this local fact in a cyclic extension without
proving it there. The local fact needs no cyclic or Galois assumption:
the existing proof uses the inverse function theorem for nonzero-degree
powers near one in complete characteristic-zero fields, together with
the norm-of-base-scalar identities and positivity of the actual local
degrees. This explains the general extension scope of the proposition.
