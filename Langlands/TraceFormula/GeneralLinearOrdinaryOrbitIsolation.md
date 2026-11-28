# Isolating one rational class of the norm-one group by a cutoff at a finite place

Let `C` be a compact set of the norm-one subgroup of the adelic points of `GL_n` over a number
field `K` whose points are regular elliptic at a finite place `v`.
`exists_finite_ordinary_normOneClasses'` gives finitely many rational norm-one elements meeting
every rational class some conjugate of which enters `C`: it applies
`generalLinearEllipticClassFiniteness` to the image of `C` in the adelic matrix group and
carries the rational representatives back to the norm-one group.
`localProjection_finite_rational` identifies the component at `v` of a rational matrix with
its image in `GL_n(K_v)`.

`ordinaryOrbitIsolation` proves: for a rational element `q₀` that is regular semisimple and
lies at `v` in an open set `V`, there is a compact clopen `U ⊆ V` containing `q₀` at `v` such
that, for every function `f¹` on the norm-one group supported in `C` and whose nonzero values
have their component at `v` in `U`, every rational element with a conjugate at which `f¹`
does not vanish is rationally conjugate to `q₀`. The set `U` comes from
`exists_rationalRegularOrbitCutoff`, which separates the class of `q₀` from the classes of the
finitely many representatives; `isTwistedConjugate_of_finiteSupportCutoff'` reduces an
arbitrary rational element to one of them.

This is the separation of one elliptic class by a test function at an auxiliary place used in
Arthur–Clozel (1989), Chapter 1, proof of Lemma 6.5 (printed pp. 54–55).
