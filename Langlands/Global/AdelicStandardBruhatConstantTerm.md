# The constant-term formula indexed by minimal Weyl elements

`StandardBruhatConstantTermData` gives a Coxeter realization on the
actual relative Weyl group and a rational normalizer representative of
each minimal double-coset element. The source and target intersections
are the Coxeter intersection subsets for the two standard parabolics.
`piece` uses those subsets to obtain the actual smaller parabolics
and the conjugation between their Levis.

`FullSourceIndex` selects the Weyl elements whose source intersection is
the original inducing parabolic. `sourceIndex_eq_iff` identifies that
condition with the Weyl action carrying the source Levi simple roots
into the target Levi simple roots. The proof uses the Coxeter criterion
for conjugation of simple reflections and positivity at a
minimal-length representative.

For each index, `summand` is the series over the rational cosets of its
target intersection parabolic. Its terms are the intertwining integrals
of the constant term of the inducing form along the source intersection,
with the source spectral parameter restricted there. The proof of
`standardBruhatConstantTerm` applies the constant-term theorem to these
actual rational representatives and their geometric-lemma data. The
result includes absolute summability of every relative series and
integrability of the intertwining integrands at every ambient point in
the convergence chamber.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 6–7 and 16,
particularly (4.2). The underlying convergence formula is Bernstein
and Lapid, *On the meromorphic continuation of Eisenstein series*,
Lemma 6.10 and (6.17).
