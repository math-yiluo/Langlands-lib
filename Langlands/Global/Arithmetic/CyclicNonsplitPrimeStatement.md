# Nonsplit finite primes in nontrivial cyclic extensions

`Langlands.Global.CyclicNonsplitPrimeStatement.{u,v}` states the following
proposition. Let `F : Type u` and `E : Type v` be number fields with the given
`Algebra F E`, and suppose `E/F` is Galois, its actual automorphism group
`E ≃ₐ[F] E` is cyclic, and `1 < Module.finrank F E`. For every finite set `S`
of nonzero prime ideals of `𝓞 F`, there are a prime `v ∉ S`, a nonzero prime
ideal `w` of `𝓞 E`, and a witness `h : w.asIdeal.LiesOver v.asIdeal` such that

`Module.finrank (v.adicCompletion F) (w.adicCompletion E) ≠ 1`.

Both prime types are `IsDedekindDomain.HeightOneSpectrum`. The completions are
the actual adic completion fields. Installing `h` with `letI` selects the
published `AdelicFunctoriality.FiniteExtension` algebra, constructed by
continuously extending the original field embedding. The number fields have
independent universes. Their number-field structures imply finiteness of the
global extension, and the published completion infrastructure supplies the
finite-dimensional local extension. Thus the displayed finrank is an actual
positive local degree, and its inequality to one expresses nontriviality of
that completed extension. No arbitrary local algebra is quantified over.

The quantifier over every finite set expresses infinitude: a finite set of all
such primes would contradict the conclusion for that set, while an infinite
set cannot be contained in any `S`. Taking `S = ∅` gives a single nonsplit
finite prime. The statement asserts no unramifiedness, no full global degree
at the selected prime, and no assertion that the prime remains prime. The
published identity `AdelicFunctoriality.localDegree_eq` identifies its local
degree with ramification index times inertia degree.

This file defines a proposition; it does not prove it. Its only hypotheses are
the field and extension structures above and the strict global-degree bound.
It assumes no first inequality, norm-index bound, approximation theorem,
prime-existence statement, or Chebotarev theorem.

## Source and correspondence

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea, 2009,
Chapter V §4, Theorem 2, printed page 17 (PDF page 26), with the preceding
first-inequality discussion on printed page 16 (PDF page 25). It is registered
as `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.

Theorem 2 gives infinitely many primes that do not split completely in a
nontrivial normal extension of global fields. It also describes this in terms
of nontrivial completed extensions. The Lean proposition specializes to cyclic
Galois extensions of number fields, uses global degree greater than one for
nontriviality, and expresses completed nontriviality by local degree different
from one. In a Galois extension the local degrees above a fixed prime agree,
so existence of the displayed `w` detects failure of complete splitting.
Number fields have only finitely many infinite places; discarding those from
the source's infinitude leaves the finite-place assertion formulated here.

Artin–Tate's cyclic proof uses the first inequality and approximation to show
that, if almost all completed extensions were trivial, every base idele would
be a principal idele times a norm, forcing global degree one. That proof is
source context only; no part of that argument is supplied as a Lean proof or
assumed as an extra hypothesis in this proposition.
