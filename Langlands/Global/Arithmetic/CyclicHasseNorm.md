# The Hasse norm theorem for cyclic extensions of number fields

`CyclicNumberFieldHasseNormStatement` uses a finite Galois extension `E/F`
of number fields with cyclic Galois group. For a unit `a` of `F`, suppose
its image is a determinant norm of a unit in `E_w` over `F_v` for every
pair `w` above `v` at finite and infinite places. Then `a` is the
determinant norm of a unit of `E`. This is the local-to-global direction
of the Hasse norm theorem, expressed using the individual field
completions. The fields lie in the same universe. See Platonov and
Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.3, Corollary
to Theorem 6.11, printed p. 308.

The implemented proof chooses a cyclic coordinate on `Gal(E/F)` and
forms the relative degree-two carry class of `a` with coefficients
in `Eˣ`. At each finite place its restriction is the carry class of
the image of `a` for the coordinate restricted along the decomposition
map. That coordinate is injective. The local norm criterion makes
this class zero.

At the infinite places a trivial stabilizer gives a zero invariant.
A nontrivial stabilizer element acts by complex conjugation, so the
place of `E` is complex and the place of `F` is real. The actual
completion ring isomorphisms carry the determinant norm to the
usual norm from `ℂ` to `ℝ`. The norm is nonnegative and the sign in
the archimedean invariant is zero. The global degree-two local-to-global
criterion for units makes the original carry class zero. Its norm
criterion produces the global norm witness. This arithmetic result
supplies the norm input for quadratic norm-kernel centers in the
adjoint Hasse argument.
