# Noetherian affine-base models of line-bundle Hom

`Langlands.AlgebraicGeometry.Picard.LineHom.NoetherianModelStatement` is an
internal intermediate proposition of the proof of
`Picard.ProperLineBundleHomRepresentabilityStatement`.

For every noetherian commutative ring `R`, every proper flat morphism
`p : Y ⟶ Spec R`, and all `Y`-modules `L` and `M` that are locally free of
rank one (`Picard.IsLocallyFreeRankOne`), it asserts
`FiniteLinearEquations.HasModel (CoherentSheaves.intrinsicModuleHomPresheaf p L M)`:
there are `m n : ℕ` and a matrix `a : Fin m → Fin n → R` with a natural
isomorphism, on the entire slice `Over (Spec R)`, from the presheaf of all
ordinary module maps between the pullbacks of `L` and `M` to the presheaf of
solutions of the homogeneous linear system `a`.

Provenance: this is the noetherian affine-base case of Stacks Project
Proposition 99.3.10 (Tag 08K6) specialized to two invertible modules; it is
derived and internal to this proof, splitting it into the noetherian model
and the reduction of the general case to it.

The single-matrix formulation is an internal constructive refinement of the
source's representability conclusion; the source proposition does not itself
choose such a matrix over the whole affine base. Proving this refinement
requires the rank-one cohomology comparison and a conversion from a bounded
finite projective representative to finite free linear equations. Those
arguments remain proof obligations in this statement module. The supporting
`LineHom.Reduction` module proves the conditional implication from this
refinement to the exact arbitrary-base target, using actual line-bundle
descent and full-slice gluing.
