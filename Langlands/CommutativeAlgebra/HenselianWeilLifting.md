# Smooth lifting through finite projective Weil restriction

This derived helper combines the published Henselian smooth section theorem
with the published algebraic Weil restriction construction and its smoothness
instance. It does not assume that the finite projective algebra is Henselian.

For a Henselian local commutative ring `R`, a surjective `R`-algebra map to a
field `k`, a finite projective commutative `R`-algebra `B`, and a smooth
commutative `B`-algebra `C`, the theorem
`HenselianSections.exists_lift_of_finite_projective_smooth` lifts each
`B`-algebra map `C → B ⊗[R] k` to a `B`-algebra map `C → B`. The composite of
the lift with the canonical map `B → B ⊗[R] k` is the given map. All four
carriers range over the same arbitrary universe.

The definition `HenselianSections.finiteProjectiveSmoothLift` chooses such a
lift, and `HenselianSections.finiteProjectiveSmoothLift_spec` proves its exact
reduction equation.

The implemented proof forms `Langlands.Algebra.WeilRestriction R B C`, which is
smooth and finitely presented over `R`. The representing bijection changes the
given map into a `k`-point of this algebra. The theorem
`HenselianSections.exists_lift_of_smooth` lifts that point to an `R`-point.
The inverse change of points gives a map to `B ⊗[R] R`, and the right unit
equivalence gives the required map to `B`. Naturality of the representing
bijection, together with the right unit equivalence, proves the stated exact
reduction equation.

The provenance is internal: the helper is a direct composition of the imported
Library results and the tensor product unit equivalence. No additional
literature assertion is introduced.
