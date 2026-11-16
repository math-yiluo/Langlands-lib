# The finite part over a Henselian local ring

`Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart f U` describes an
actual open subscheme `U` of `X`, where `f : X → Spec R` and `R` is a
commutative local ring. It requires that the underlying open set is also
closed, that the composite `U → X → Spec R` is finite, and that every
point of `X` mapping to the closed point of `Spec R` belongs to `U`.
Thus its closed fibre is the full closed fibre of `X`. These conditions do
not specify a group structure.

`HenselianFinitePartStatement.{u}` asserts that such an open exists when
`R : Type u` is Henselian local and `f` is finite type, locally quasi-finite
and separated. It concerns schemes in the same arbitrary universe `u`.
The proposition is a statement only; this module supplies no existence proof.

The source is A. Grothendieck and J. Dieudonne, *Elements de geometrie
algebrique IV, Quatrieme partie* (1967), Theorem 18.5.11(c), printed
pp.130–132 (zero-based PDF pages128–130). That theorem gives, at each
quasi-finite point of the closed fibre of a separated locally finite-type
scheme over a Henselian local ring, a finite open and closed summand.
The statement here is its derived whole-fibre form: the closed fibre of a
finite-type locally quasi-finite map is finite, so the finitely many local
summands give the required finite clopen part. Mathlib's
`LocallyQuasiFinite` alone includes neither quasi-compactness nor locally
finite type; the separate `LocallyOfFiniteType` and `QuasiCompact` hypotheses supply both here.
The original volume's *Errata et addenda, Liste 3*, printed pp.349–360,
was checked; no correction to Theorem 18.5.11 was found there.

This is the scheme-level existence input for removing the finite part of
a fibrewise-isogeny kernel over a Henselian DVR. Group operations,
normality, flatness and local finite presentation of that part remain
separate obligations. The statement does not assert the existence of a
finite normal kernel subgroup or the reductive fibrewise-isogeny theorem.
