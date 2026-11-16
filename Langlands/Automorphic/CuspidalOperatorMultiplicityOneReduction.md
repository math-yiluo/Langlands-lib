# Cuspidal operator multiplicity one from comparison of actual Whittaker functions

Worker 805. This is an internal reconstruction reduction for
`Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement`, retaining the
unproved `CuspidalWhittakerModelComparisonStatement`.

The comparison states that each full operator equivalence between actual cuspidal
realizations transports their actual Whittaker functions up to one complex scalar,
independent of the vector and adelic point, for every standard global additive
character. It asserts neither algebraic Whittaker uniqueness on arbitrary
Harish-Chandra modules nor the existence of a smooth globalization.

The proof uses the published exact cusp expansion to reconstruct proportional
actual functions by uniqueness of sums. The faithful inclusions identify their
vectors in the common space of stable automorphic functions. The scalar is
nonzero because the equivalence is surjective and the target space is nonzero.
Closure under scalars, using the inverse scalar for one inclusion, then identifies
the two subspaces.

This is the reconstruction part of Cogdell (2004), printed pp.201–202, and
Getz–Hahn (2024), Theorem 11.4.3, printed p.303 (PDF p.314), after the analytic
comparison of Whittaker functions. Shalika (1974), Theorem 5.5, printed pp.187–188
(PDF pp.18–19), derives the comparison using continuous functionals and a Sobolev
estimate before Fourier reconstruction (Theorem 5.9). These sources are registered
as `cogdell-2004-analytic-theory-gln`, `getz-hahn-2024-automorphic-representations`
and `shalika-1974-multiplicity-one`. The registered October 2026 Getz–Hahn errata,
pp.1–3, contain no change to Theorem 11.4.3.

The exact unconditional target remains open. The analytic comparison premise must
still account for the passage from the Library's finite, compact and differential
operators to continuous Whittaker functionals on a suitable smooth completion.
