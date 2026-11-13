# Proof: the index of the semisimple anisotropic kernel is the subdiagram on `Δ₀`

Author: Worker 146 (Task 5619).

`Langlands.GroupScheme.titsAnisotropicKernelIndex` proves exactly the published
proposition `Langlands.GroupScheme.TitsAnisotropicKernelIndexStatement.{u}`
(module [`TitsIndexAnisotropicKernelStatement`](TitsIndexAnisotropicKernelStatement.md)).
It keeps the universe parameter `u` and takes no hypotheses.

## Statement

Fix a field `k : Type u` of any characteristic, a `k`-group `G` whose structure
morphism is affine and locally of finite type, and actual index data
`d : TitsIndexData G` with maximal split torus `S`. Let `j : M ⟶ G` represent
`torusCentralizer d.splitInclusion`, and let `i : D ⟶ M` satisfy
`IsDerivedSubgroup i`. The theorem gives instances `IsAffineHom D.X.hom` and
`LocallyOfFiniteType D.X.hom`, index data `e : TitsIndexData D`, and a proof of
`d.KernelComparison (i ≫ j) e`. There are a torus map `τ : T_D ⟶ T` and an
equivalence `φ` from the roots of `e` onto the roots of `d` with zero
restriction to `S`, satisfying the six conjuncts:

1. the square `T_D ⟶ T ⟶ G` = `T_D ⟶ D ⟶ G`;
2. each root of `e` is the restriction along `τ_{k_s}` of the corresponding root
   of `d`;
3. each coroot of `e`, pushed forward along `τ_{k_s}`, is the corresponding
   coroot of `d`;
4. the Cartan pairings agree;
5. `φ` carries the base of `e` onto `Δ₀`;
6. `φ` intertwines the full star actions on simple vertices.

## Proof

The theorem is the term
`titsAnisotropicKernelIndex_of_anisotropicKernel titsAnisotropicKernel`.

- `titsAnisotropicKernel` is the published proof of
  `TitsAnisotropicKernelStatement`
  ([`TitsIndexAnisotropicKernelProof`](TitsIndexAnisotropicKernelProof.md),
  Worker 145, Task 5618): `D` is semisimple and anisotropic.
- `titsAnisotropicKernelIndex_of_anisotropicKernel`
  ([`TitsKernelIndexData`](TitsKernelIndexData.md)) derives the index statement
  from that one. Its proof, with the exact construction of `e`, `τ` and `φ`, is
  described in that module's Markdown. In outline:
  - `T_D` is the full scheme-theoretic intersection `T ∩ D` inside `M`. It is a
    maximal torus of `D` ([`TitsKernelTorus`](TitsKernelTorus.md)), and `τ` is
    its first projection.
  - Over `k_s = SeparableClosure k`, the roots of `D` are the restrictions of
    the roots of `G` with zero restriction to `S`, with the matching coroots
    ([`TitsKernelRootComparison`](TitsKernelRootComparison.md)). The base of `e`
    is built from `Δ₀`. Star actions are compared through the unique based
    representative of each Weyl coset
    ([`LinearAlgebra/RootDatumZeroFace`](../../LinearAlgebra/RootDatumZeroFace.md)).
  - The maximal split torus of `e` is trivial. It is maximal because `D` is
    anisotropic, and this is the only use of `titsAnisotropicKernel`.

The proof keeps the arbitrary universe and works over every field, in every
characteristic. It uses only published Library results and Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). Its transitive imports do
not reach `LocalRankOneClassificationStatement` or any local Kneser–Tits
statement or result. No simply connected cover is involved.

## Relation to the literature

J. Tits, *Classification of algebraic semisimple groups* (1966), §2.2 and the
second-to-last paragraph of §2.3 (printed p. 39), registered as
`tits-1966-classification-algebraic-semisimple`, states the following without
proof. `Δ₀` is the set of simple roots of `𝒟𝒵(S)` with respect to the maximal
torus `T ∩ 𝒟𝒵(S)` and a suitable ordering. The index of the semisimple
anisotropic kernel is obtained from that of `G` by deleting the vertices outside
`Δ₀`. The Lean proof realizes this with Tits's maximal torus `T ∩ 𝒟𝒵(S)`, the
ordering induced by the base of `d`, and the actual star actions of both index
data.
