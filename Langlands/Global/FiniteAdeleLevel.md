# Actual finite-adelic rings at a finite set of places

Author: Worker 208.

Let `R` be a commutative Dedekind domain with fraction field `K`, in an
arbitrary common universe `u`. For a finite set `S` of height-one primes,
`finiteAdeleLevel R K S` is the actual subring of Mathlib's
`IsDedekindDomain.FiniteAdeleRing R K` consisting of adeles integral at every
prime outside `S`. The local fields and integer rings are the existing
`v.adicCompletion K` and `v.adicCompletionIntegers K`, rather than an assumed
family of fields.

`isOpen_finiteAdeleLevel` obtains openness from the existing
restricted-product theorem and openness of each completed valuation ring.
`finiteAdeleLevelMap` is the inclusion when `S ⊆ T`, and its coercion
formula identifies it with the inclusion in the same actual finite adele
ring.

`finiteAdeleLevelDiagonal` maps the actual Mathlib ring of `S`-integers,
`(S : Set (HeightOneSpectrum R)).integer K`, diagonally into this subring.
The proof that the image lies there uses the defining valuation
inequalities of `S`-integers and agreement of global and completed
valuations. This ring map defines the displayed `S`-integer algebra
structure. Its component formula is the usual map through `K` to each
completion.

`finiteAdeleLevelProductEquiv` is an explicit ring isomorphism to the
product of the completions at primes in `S` and the completed integer
rings at primes outside `S`. Its inverse `finiteAdeleLevelAssemble` joins
the two families. The exceptional set of nonintegral coordinates is
contained in the finite set `S`, which proves that the assembled family
is an actual finite adele. The inverse laws are coordinatewise; the
forward map preserves addition and multiplication by their componentwise
definitions. The two final formulas identify its components with the
actual adelic projections. This file does not assert that the ring
isomorphism is a homeomorphism.

This is derived arithmetic infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
the definition of `A_{F,S}`, and printed pp.6–8, Theorem 3.6 and its local
product factors. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The general Dedekind-domain finite sector isolates the arithmetic product
construction used in that theorem.

The finite set of height-one primes here can be empty. It describes only
the primes of `R`; it does not replace Conrad's convention that the full
set of global places is nonempty and contains the archimedean places.
For a number field, `R = NumberField.RingOfIntegers K` gives its actual
finite-adelic sector, and the archimedean factor must still be included
to obtain `A_{K,S}`. For a global function field, a suitable Dedekind model,
the omitted places and their actual completions must still be supplied and
proved to recover all global places. This file imposes no separability
condition on `K` but assumes the displayed Dedekind-domain and
fraction-field instances. It does not construct those instances for every
function-field presentation. It proves no full global-field realization,
adelic colimit, scheme-point comparison or change-of-model theorem.
