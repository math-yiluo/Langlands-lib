# Weak base change of sums of isobaric data

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter III, Theorem 4.2(c), use the
cuspidal lifts from parts (a) and (b) and combine them by parabolic
induction (printed p. 206).
`IsobaricData.UnitaryWeakBaseChangeSumStatement F E` formulates that step
on constituent data for any number-field extension `E/F` with compact
adelic quotients.
If every unitary singleton over `F` admits a unitary weak base change to
`E`, then every unitary isobaric datum over `F` admits one.

`IsobaricData.isWeakBaseChangeOf_zero` uses rank-zero systems with empty
exceptional sets on both fields. The empty constituent enumeration
attaches each system, and the two spectra at every tested place are
empty. The unramified places used in the weak transfer relation are
cofinite by `AdelicFunctoriality.eventually_ramificationIdx_eq_one`.

`IsobaricData.IsWeakBaseChangeOf.add` concatenates the two actual
constituent enumerations on each field, pairing each constituent with
its spectral attachment during concatenation. The Euler polynomial of
the resulting direct sum is the product of the two polynomials. At the
common good places the residue-degree power commutes with direct sum,
so the sums satisfy weak base change. Both the sums of constituents and
the sums of spectra retain repeated terms.

`IsobaricData.exists_unitary_weakBaseChange_of_singletons` inducts on the
input multiset, using the empty transfer and closure under addition.
Each lifted term is unitary by the singleton hypothesis, and unitarity
of the sum follows constituent by constituent. The two field universes
and the two presentation-carrier universes are independent throughout.
