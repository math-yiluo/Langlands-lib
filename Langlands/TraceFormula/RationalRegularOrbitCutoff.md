# A compact open cutoff for finite lists of rational classes

`rationalRegularOrbitCutoff` proves `RationalRegularOrbitCutoffStatement`.
Let `K → F` be a field embedding, where `F` has a Hausdorff ring
topology and `GL_n(F)` is locally compact and totally disconnected
in its matrix group topology. Given a regular semisimple rational
matrix `γ` and an open neighbourhood `V` of its image in `GL_n(F)`,
the lemma chooses a compact open neighbourhood `U ⊆ V` of that
image. The ordinary local orbit of a matrix in the supplied finite
rational list can meet `U` only when the matrix is rationally
conjugate to `γ`.

One cutoff also works for a list of rational twisted classes in a
cyclic extension `L/K`. Their associated base matrices are included in
the list to which the ordinary cutoff is applied. If the orbit of an
associated base matrix meets `U`, its rational conjugacy to `γ` gives
conjugacy of the two cyclic norm matrices over `L`. The Library's
cyclic norm lemma then gives rational twisted conjugacy to the
specified upper matrix `δ` associated with `γ`.

To construct `U`, the proof removes the fibers of all competing
characteristic-polynomial coefficient tuples from `V`. The
competing tuples form a finite closed set in the Hausdorff
coefficient space, and the coefficient map is continuous.
Equality of tuples over `F` implies equality of the
rational characteristic polynomials by injectivity of `K → F`.
The regular semisimple conjugacy theorem then gives the rational
conjugator. The locally compact, Hausdorff and totally disconnected
matrix group has a compact clopen neighbourhood inside the
remaining open set.

This is the finite-list separation step in the orbit isolation used
by Arthur–Clozel, Chapter 1, pp. 43 and 46, and Henniart–Lemaire,
I.6.8, pp. 49–50 (PDF pp. 57–58). The finite lists, the realization
of the cutoff by split matching test functions, and the trace
formula measure comparison are separate inputs to the global
argument.
