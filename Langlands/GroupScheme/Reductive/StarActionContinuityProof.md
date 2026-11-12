# Continuity of the star action: proof

Authors: Worker 3483 (formerly Worker 15; Lean proof and original exposition) and
Worker 119 (dependency documentation and exact-target submission). `Langlands.GroupScheme.starActionContinuity` proves
`Langlands.GroupScheme.StarActionContinuityStatement.{u}` exactly, with no
added hypotheses or proposition-valued inputs. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

Let `E/k` be algebraic and `d : GaloisPinningData k E G`. Apply
`torusLatticeGaloisContinuity` (module `Torus/LatticeGaloisContinuityProof`) to the
torus `T` of `d`, which splits over `E` (`d.isSplitTorus`). This gives a
finite-dimensional intermediate field `L` such that every automorphism fixing `L` acts
trivially on `X^*(T_E)` and `X_*(T_E)`.

Let `σ` fix `L` pointwise. Then `σ⁻¹` also fixes `L`. The three components of
`d.galoisAction σ` are as follows.

- The weight map is `characterLattice.galoisRepresentation σ`, which is the identity.
- The coweight map is `cocharacterLattice.galoisRepresentation σ⁻¹`, which is the
  identity.
- The root permutation is `IsRootDatumOf.galoisRootIndexEquiv σ`. By
  `IsRootDatumOf.galoisRootIndexEquiv_root` it sends a root index `j` to the index of
  `σ (P.root j) = P.root j`, so it is the identity by injectivity of `P.root`.

These are the definitional components of
`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus`; the proof uses `change`
to expose them. Hence `d.galoisAction σ = 1`.
`d.starAction σ` is `basedRootDatumProjection (d.galoisAction σ)`, and a monoid
homomorphism sends `1` to `1`.

## Inputs and provenance

The proof is reused without Lean changes from Task 3483 draft revision 3, task
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, directory
`revision-3-ce01aee184dec1c896d6b5edb977d87b1fc08762357b7999f699a7d8b24f5d12/files/`.
The unchanged target module
`Langlands.GroupScheme.Reductive.StarActionStatement` documents the source
assertion and original-literature provenance. The implemented proof is the
formal deduction from torus-lattice continuity described above.

Every project input theorem is named here with its module:

| Declaration | Module | Use |
| --- | --- | --- |
| `Langlands.GroupScheme.torusLatticeGaloisContinuity` | `Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof` | One finite-dimensional field makes both lattice actions trivial; this proof is submitted separately as target 1 of Task 5263. |
| `Langlands.GroupScheme.IsRootDatumOf.galoisRootIndexEquiv_root` | `Langlands.GroupScheme.Reductive.RootDatumGaloisRoots` | The root-index action agrees with Galois action on the root embedding. |

The proof unfolds the published constructions
`Langlands.GroupScheme.GaloisPinningData.galoisAction`,
`Langlands.GroupScheme.GaloisPinningData.starAction` and
`Langlands.GroupScheme.GaloisPinningData.toSplitPinning`
(`Langlands.GroupScheme.Reductive.StarAction`), and
`Langlands.GroupScheme.IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus`
(`Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots`). It uses
`Langlands.GroupScheme.SplitPinning.basedRootDatumProjection`
(`Langlands.GroupScheme.Reductive.BasedRootDatumProjection`) as a monoid
homomorphism. Extensionality of the root-pairing equivalence comes from
`Mathlib.LinearAlgebra.RootSystem.Hom`; root injectivity is part of the root
embedding in `Mathlib.LinearAlgebra.RootSystem.Basic`. The final equality uses
Mathlib's `map_one`, supplied by `Mathlib.Algebra.Group.Hom.Defs`, and the inverse
fixer calculation uses `AlgEquiv.symm_apply_eq` from
`Mathlib.Algebra.Algebra.Equiv`.
