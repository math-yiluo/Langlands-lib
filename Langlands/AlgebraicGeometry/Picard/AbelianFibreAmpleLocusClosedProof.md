# Closedness of the abelian ample-fibre locus: proof

Author: Worker 5715.

This module proves
`Langlands.AlgebraicGeometry.Picard.AbelianFibreAmpleLocusClosedStatement`
as the theorem
`Langlands.AlgebraicGeometry.Picard.abelianFibreAmpleLocusClosed`.

Let `S` be a locally noetherian scheme, `A` an abelian scheme over `S`, and
`L` a line bundle on the total space of `A`. Then the set of points `s` of `S`
at which the fibre of `L` over `s` is ample is closed in `S`.

The proof has two parts.

- A reduction, proved in this module, of the closedness statement to the
  published DVR statement
  `Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationStatement`.
  The reduction adds no hypothesis to either statement.
- The published Library proof `dvrAbelianAmpleSpecialization` of that DVR
  statement (module
  `Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationProof`,
  Task 5873, by Worker 171). This module imports it and does not reprove it.

## Topological lemma

`isClosed_of_isOpen_of_stableUnderSpecialization_of_noetherianCover` makes
these assumptions:

- `X` is a quasi-sober `T₀` space;
- every point of `X` lies in an open subset that is a noetherian space.

Under them, an open set `Z` that is stable under specialization is closed.

The Lean proof goes as follows. Let `x` lie in the closure of `Z`, and let `U`
be an open noetherian neighbourhood of `x`.

1. The subspace `Y = Z ∩ U` is noetherian
   (`NoetherianSpace.inter_of_right`).
2. `Y` is quasi-sober, because it is an open subspace of a quasi-sober space
   (`IsOpenEmbedding.quasiSober`).
3. `Y` therefore has finitely many generic points of irreducible components
   (`genericPoints.finite` with `NoetherianSpace.finite_irreducibleComponents`).
4. The closure of these generic points is all of `Y`
   (`genericPoints.closure`).
5. Because `U` is open, `x` lies in the closure of `Y`.
6. Hence `x` lies in the closure of the image of these finitely many generic
   points. That closure is the finite union of their point closures
   (`Set.Finite.closure_biUnion`).
7. So some generic point `g` of `Y` specializes to `x`. Since `g ∈ Z` and `Z`
   is stable under specialization, `x ∈ Z`.

## Scheme lemma

`isClosed_of_isOpen_of_stableUnderSpecialization_of_isLocallyNoetherian`
applies the topological lemma to the underlying space of a locally noetherian
scheme `S`. Mathlib's scheme instances supply quasi-sobriety and `T₀`. For the
cover:

- every point has an affine open neighbourhood
  (`exists_isAffineOpen_mem_and_subset`);
- its ring of sections is noetherian (`IsLocallyNoetherian.component_noetherian`);
- so the neighbourhood is a noetherian space (`noetherianSpace_of_isAffineOpen`).

## Main reduction

`abelianFibreAmpleLocusClosed_of_dvrSpecialization` proves
`DvrAbelianAmpleSpecializationStatement.{u} → AbelianFibreAmpleLocusClosedStatement.{u}`.

Let `S` be locally noetherian, let `A` be an abelian scheme over `S`, and let
`L` be a line bundle on `A.X.left`. The target set is definitionally the
Library's `ampleFibreLocus A.X.hom L`.

- **Openness.** Since `A.X.hom` is proper, `isOpen_ampleFibreLocus` (which
  uses the published `properFibreAmpleSpreading`) shows that the locus is open.
- **Stability under specialization.** Let `η ⤳ s` with `η` in the locus. If
  `η = s` there is nothing to prove. Otherwise `nonempty_dvrSpecialization`
  gives a discrete valuation ring `D.ring` and a morphism
  `D.map : Spec D.ring ⟶ S`. It sends the zero prime to `η` and the closed
  point to `s`.
- **Base change.** Let `B` be the Library base change
  `(AbelianScheme.baseChange D.map).obj A`. Its total space is
  `pullback A.X.hom D.map` and its structure map is the second projection. Let
  `LB` be the pullback of `L` along the first projection.
- **Transporting the fibre conditions.** The Cartesian square
  `IsPullback.of_hasPullback A.X.hom D.map` and the Library lemma
  `mem_ampleFibreLocus_iff_of_isPullback` identify membership of a point `t`
  of `Spec D.ring` in the ample-fibre locus of `(B, LB)` with membership of
  `D.map t` in the ample-fibre locus of `(A, L)`. That lemma covers the
  residue-field extension through field base change and its reflection.
  - Applied at the zero prime, the hypothesis on `η` gives ampleness of the
    generic fibre of `LB`.
  - The supplied DVR statement then gives ampleness of the closed fibre.
  - Applied at the closed point, this gives ampleness of the fibre of `L`
    at `s`.
- **Conclusion.** The locus is open and stable under specialization, so the
  scheme lemma shows it is closed.

## Final theorem

`abelianFibreAmpleLocusClosed : AbelianFibreAmpleLocusClosedStatement.{u}` is
the main reduction `abelianFibreAmpleLocusClosed_of_dvrSpecialization` applied
to the Library theorem
`dvrAbelianAmpleSpecialization : DvrAbelianAmpleSpecializationStatement.{u}`,
at the same universe `u`.

## Provenance

The specialization criterion for closedness is standard point-set topology for
locally noetherian schemes; the argument above is internal. The decomposition
into openness and DVR specialization follows the route stated in the Markdown
of the published `DvrAbelianAmpleSpecializationStatement`. That Markdown
derives the statement from Faltings–Chai, *Degeneration of Abelian Varieties*
(1990), Chapter I, Remark 1.10(b), printed p. 7. This module does not use the
dual-scheme or Picard-representability constructions. It also does not use any
of the statements listed as consumers of the closedness target.
