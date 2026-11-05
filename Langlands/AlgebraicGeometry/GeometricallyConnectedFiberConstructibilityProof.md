# Local constructibility of actual geometric-connectedness fibre loci

Worker 1447 proves the published proposition
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.GeometricallyConnectedFiberLocalConstructibility.{u}`
in every universe `u`. For any morphism `f : X ⟶ Y` of schemes, assuming
`LocallyOfFinitePresentation f`, `QuasiCompact f` and `QuasiSeparated f`, the
actual subset `geometricallyConnectedFiberLocus f` of `Y` is locally
constructible. The published statement and its import closure are unchanged.

Membership at `y : Y` means geometric connectedness of the structure morphism
of the actual residue-field scheme fibre at `y`. The geometric connectedness
condition tests field-valued base changes and includes nonemptiness. Thus an
empty geometric fibre does not belong to the locus. The theorem applies to
arbitrary schemes and adds no affine, separated, proper, smooth, flat,
Noetherian or surjectivity hypothesis.

The Lean proof applies the published reduction
`geometricallyConnectedFiberLocalConstructibility_of_generic_splitting`,
developed by Worker 105, to three published unconditional theorems:

- `finiteTypeFiniteEtaleGenericComponentSplitting`, the finite étale splitting
  of actual generic-fibre components proved by Worker 27 using the published
  field-splitting and prescribed-cover results;
- `finiteTypeGeometricallyIrreducibleGenericSpreading`, the spreading theorem
  proved by Workers 1606 and 336;
- `ComponentIncidence.finiteClosedGeometricallyConnectedCoverCriterion`,
  the actual finite closed-cover criterion supplied by Worker 105 and
  checked and submitted by Worker 1437.

The reduction splits the actual generic irreducible components, spreads their
geometric irreducibility, and compares the incidence of the resulting finite
closed cover. Descent through the open image of the cover gives constancy of
the geometric-connectedness truth value near a generic point of a Noetherian
base. Applying this to the reduced induced schemes of irreducible closed
subsets and using Noetherian closed-subset induction gives constructibility
over Noetherian bases. The existing actual finite-presentation approximation
and affine-cover comparison then give local constructibility over arbitrary
targets. All three geometric premises of this reduction are discharged by
the imported proofs.

The mathematical source is the geometric-component-count-one consequence of
Stacks Project Lemma 37.28.6 (055I), with the counting convention of Lemma
37.28.3 (055F), in the registered collection
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
The retained files are `055I.html`, including the terminology comments, and
`055C.html`. The count is taken after a separably closed residue-field
extension. Count one therefore agrees with the nonempty geometric
connectedness used here. The implemented proof uses the published Boolean
generic-constancy reduction rather than constructing the full count function.

The published globalization theorem can now turn this local conclusion into
constructibility when the target is quasi-compact and quasi-separated.
Pure-dimension constructibility, the unrestricted original-ring filtered
descent theorem and whole-paper coverage remain separate obligations of
the parent program.
