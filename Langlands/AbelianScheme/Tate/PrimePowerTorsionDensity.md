# Density and homomorphism detection for actual prime-power torsion

The theorem `PrimePowerTorsion.dense_locus A p` proves density of actual
geometric prime-power torsion for any abelian scheme over the spectrum of an
algebraically closed characteristic-zero field, at every natural prime `p`.
All declarations retain the arbitrary universe `u`.

The helper `levelComparison` works over every field and for any natural `p`.
A closed immersion `f : B ⟶ A` whose image contains the torsion locus gives
a bijection on the existing actual level groups at every order `p ^ n`.
Injectivity is cancellation through the immersion. For surjectivity, a
torsion section into `A` factors through `B` because the test field spectrum
is reduced and its image lies in the immersion's image. Cancellation shows
that its lifted section is killed by the same power.

For density, `closureAbelianScheme_exists` realizes the closure as a
closed abelian subscheme `B` of `A`. Both abelian schemes have finite
relative dimensions `gB` and `gA`. The published torsion-count formula,
with the proved cube-pullback and ample-existence inputs, gives respectively
`p ^ (2 * gB)` and `p ^ (2 * gA)` points in their prime torsion groups.
The bijection at level `p ^ 1` equates these cardinalities. Since `p ≥ 2`,
injectivity of natural powers gives equal dimensions. The published
`fieldEqualDimensionClosedImmersion` theorem makes the closed immersion an
isomorphism. Its image, previously identified with the torsion closure,
is therefore all of `A`.

The helper `hom_eq_zero_of_dense_locus` needs only a field, a natural `p`,
and explicit density of the torsion locus of `A`. If every actual
prime-power level map of `f : A ⟶ B` is zero, the equalizer of `f` and zero
contains all the torsion sections. The density hypothesis makes that
equalizer dominant. Smoothness makes the source reduced, and separatedness
of the target then identifies the two scheme morphisms. Extensionality
in the bundled abelian-scheme category concludes `f = 0`.

This is an internal generalization of the published two-power level comparison,
density reduction and homomorphism detection development in
`Langlands.AbelianScheme.Tate`. It reuses the general dimension and cardinality
lemmas from `TwoPowerTorsionDensityReduction`. Its literature provenance is
the prime-to-characteristic case of Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary version, Chapter V, §3,
Theorem (5.30), printed p.84 / PDF p.88
(`edixhoven-vandergeer-moonen-abelian-varieties-draft`).
The implementation proves connectedness of the closure before this comparison,
so counting torsion at the prime itself suffices.
