# Global assembly of Steinberg big-cell data from explicit inputs

Worker 1369's internal assembly reduces the unchanged
`SteinbergBigCellStatement.{u}` to four explicit global inputs. It constructs
the actual data for the original group and unpacks them into the exact
existential conclusion. It does not prove any of the four inputs and does
not prove the unconditional host statement.

`SplitSteinbergHeightIrreducibilityStatement` is a `Prop`-valued interface.
Over every algebraically closed field `k : Type u`, it quantifies over an
actual affine group `G`, a supplied split pinning `p` with a finite root
index, full integral coroot span, and a prime exponential characteristic
`q`. It requires the existing
`p.CanonicalRhoSteinbergHeightIrreducibility hspan q` interface. Thus, at
each positive height, a supplied highest-weight representation at
`(q ^ r - 1) • rho` must imply irreducibility of the actual regular rational
representation on the entire canonical covariant space in every finite
standard-indexed basis. This input neither chooses a cyclic subspace in
place of the full space nor asserts highest-weight existence.

`SteinbergBigCellInputs` is a proposition structure with four fields:

- `RootDatumExistenceStatement.{u}`, providing finite reduced root data
  for actual split maximal tori.
- `SplitSimplyConnectedCorootSpanStatement.{u}`, giving full integral
  coroot generation for a supplied finite reduced datum of an actual split
  maximal torus in a simply connected group.
- `SplitDominantHighestWeightRepresentationsExistStatement.{u}`, providing
  the full highest-weight package at every integral dominant character.
- The preceding per-height irreducibility interface.

These are premises of the construction, with no implicit claim that their
statement publications supply proofs.

`steinbergBigCellDataOfInputs` takes this structure, an algebraically closed
field in arbitrary universe `u`, a prime characteristic `q`, an actual
affine group `G`, and `IsSimplyConnected G`. Semisimplicity supplies connected
reductivity and smoothness. The published theorem
`exists_isMaximalTorus_isSplitTorus_of_isSepClosed` supplies a split maximal
torus of the original group. Algebraic closedness supplies the separable
closedness required there; no torus-existence premise is added.

`SplitPinning.ofRootDatumExistence` uses the explicit root-datum input on
that torus and the actual root-line trivializations furnished by the
published `splitRootLieLine` theorem. Its chosen base comes from the
published finite reduced integral-base construction. This gives an actual
split pinning of the same group. A `Fintype` structure is chosen on its
already finite root index.

The explicit coroot-necessity input applies to that pinning's actual torus,
finite reduced root datum and the original simple-connectedness proof.
It yields integral equality with the full cocharacter lattice. The prime
characteristic supplies exponential characteristic `q`. The constructor
then applies `canonicalRhoSteinbergBigCellData` with this pinning and span,
the supplied highest-weight input and the specialized per-height input.
The resulting data include all six previously proved geometric laws and
the full-space cofinal irreducibility law proved conditionally by the
canonical assembly. Classical choice extracts the data from the resulting
proof of nonemptiness; it supplies no mathematical input.

`steinbergBigCell_of_inputs` has type
`SteinbergBigCellInputs.{u} → SteinbergBigCellStatement.{u}`.
Its proof introduces the original target's field, characteristic and group,
applies the data constructor, and invokes `SteinbergBigCellData.exists_data`.
All relative test schemes in the target are retained, including nonaffine,
nonreduced and empty tests. The finite bases are bases of the entire
specified covariant coordinate spaces. No target or imported statement is
changed.

The provenance is an internal derivation from the imported Library
constructions and proofs. The four inputs record precisely the remaining
structural and representation-theoretic obligations of this route. An
unconditional theorem of the exact host type still requires published
proofs of those inputs.
