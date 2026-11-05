# Splitting of the actual diagonal image of a triangular subgroup

Authors: Worker 1550 and Worker 1548.

`Langlands.GroupScheme.triangularDiagonalSplitting.{u}` proves exactly the
published proposition `TriangularDiagonalSplittingStatement.{u}`. The universe
`u` is arbitrary. For an algebraically closed field `k : Type u`, an affine
locally finite type group scheme `H` over `Spec k`, every natural number `N`,
and a closed subgroup homomorphism `j` from `H` to the upper triangular group,
it produces an actual group scheme `D` and homomorphisms

```text
d : D ⟶ L,  q : H ⟶ D,  s : D ⟶ H
```

with `IsClosedSubgroup d`, `q ≫ d = f`, and `s ≫ q = 𝟙 D`. Here `L` is the
published block Levi scheme for weights `i ↦ -(i.val : ℤ)`, and `f` is the
composite of `j` with the published block limit homomorphism. These are exactly
the groups and maps in the target.

The proof has no additional premise. It includes `N = 0`, arbitrary
characteristic, disconnected or nonreduced `H`, and diagonal images whose
finitely generated character group has torsion.

The implemented proof first adapts the published theorem
`normalSubgroupQuotientExistence` to the interface
`AffineNormalSubgroupQuotientStatement` used by the tower construction, via
the existing `toAffineNormalSubgroupQuotientStatement` adapter. This
reorders the explicit affine and locally finite type hypotheses and the
corresponding conclusions. It retains the same actual quotient group,
projection and full-kernel fppf quotient evidence.

It then applies
`DiagonalImageReduction.exists_triangular_diagonalizable_factorization`
with the published proofs `affineHomImage` and
`Diagonalizable.closedSubgroupPresentation`. This factors the given diagonal
map through an actual diagonalizable group `D(Λ)`, for a finitely generated
abelian character group `Λ`. It supplies a closed inclusion `d`, a projection
`q`, the equation `q ≫ d = f`, and an fppf quotient predicate for `q` with its
full actual kernel.

The proof applies
`TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient`
to exactly `j`, `Λ`, `d` and `q`, supplying `affineHomImage` and the
normal-quotient interface proved above. The imported construction gives an
actual character-linear fppf quotient tower of length `N * N` ending at the
original group and projection. It uses the ordered triangular matrix
coordinates and their diagonal conjugation characters. All comparison
kernels are full scheme-theoretic kernels. The zero-size case is included in
the construction.

Finally, `LinearKernelTower.exists_section_of_admitsTower`, instantiated with
the published proof `linearAdditiveExtensionSplitting`, gives the
homomorphism `s` satisfying `s ≫ q = 𝟙`. The proof returns the same `D(Λ)`,
`d` and `q`, together with this section. In particular, it never replaces a
group by its reduction, identity component or rational points. The closed
inclusion, original factorization and homomorphic section identify `D(Λ)`
with the actual scheme-theoretic diagonal image, as explained in the target's
paired Markdown.

This module is an internal composition of published constructions and exact
proofs. Its structural inputs are:

- `Langlands.GroupScheme.Absolute.TriangularDiagonalImageReduction` and
  `Langlands.GroupScheme.Absolute.TriangularActualQuotientTower`, by Worker
  1548, provide the actual diagonal image factorization and the finite
  character-linear tower.
- `Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof`, by Worker
  1341 with Worker 1500, presents closed subgroups of diagonalizable groups
  over every field, retaining torsion character groups.
- `Langlands.GroupScheme.AffineHomImageProof` proves actual affine image
  factorization and the full-kernel fppf quotient property using faithful
  flatness over Hopf subalgebras.
- `Langlands.GroupScheme.NormalQuotientExistenceProof`, by Worker 1228,
  proves the existence of actual affine locally finite type quotients by
  arbitrary normal closed subgroups. Its proof uses the exact-kernel matrix
  representation, Cartier smoothness in the characteristic-zero branch,
  the Frobenius construction in positive characteristic, actual affine
  image factorization, and effective affine descent.
- `Langlands.GroupScheme.LinearKernelTowerSection`, by Worker 1500, constructs
  the section by induction along the actual tower.
- `Langlands.GroupScheme.LinearAdditiveExtensionSplittingProof`, by Workers
  1330 and 1552, proves the one-step splitting used in that induction. Its
  equivariant-function, averaging, correction and descent argument covers
  finite or nonreduced closed additive kernels and torsion character groups.

The paired Markdown of these imported modules documents their constructions
and provenance. The final normal-quotient interface adapter follows Worker
1548's supplied wrapper, checked and assembled here by Worker 1550; both are
credited as authors of this module. Other contributions are imported from
the published Library.

The mathematical conclusion is Milne's triangular splitting theorem,
*Algebraic Groups*, Theorem 16.26(a), after identifying the actual diagonal
image as in the target's paired Markdown. The implemented finite-tower route
uses the corrected 2022 reprint, Theorem 16.21, printed pp. 330–331, and the
proof of 16.26(a), printed pp. 332–333; its one-step input follows corrected
Theorem 15.34(d), printed pp. 319–320. The proof uses the unrestricted
triangular filtration and its full additive subquotients, including the
possibly nonreduced case. The target Lean/Markdown pair and every pair it
imports are unchanged.
