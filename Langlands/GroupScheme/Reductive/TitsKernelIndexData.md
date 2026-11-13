# Index data of the semisimple anisotropic kernel

Author: Worker 146 (Task 5619).

This module constructs actual index data for the semisimple anisotropic kernel
and proves the reduction

`Langlands.GroupScheme.titsAnisotropicKernelIndex_of_anisotropicKernel
  (hA : TitsAnisotropicKernelStatement.{u}) : TitsAnisotropicKernelIndexStatement.{u}`.

Both propositions are defined in
[`TitsIndexAnisotropicKernelStatement`](TitsIndexAnisotropicKernelStatement.md).
The premise `hA` is used only for anisotropy of `D`. The statement for `D`
requires a maximal split torus of `D` that lies inside the maximal torus
`T ∩ D`. The proof takes the trivial split torus, and its maximality is exactly
`IsAnisotropic D`. The premise is discharged by the published
`titsAnisotropicKernel` in
[`TitsIndexAnisotropicKernelIndexProof`](TitsIndexAnisotropicKernelIndexProof.md).

The provenance is internal: the module composes published Library results with
the helper modules [`TitsKernelTorus`](TitsKernelTorus.md),
[`TitsKernelRootComparison`](TitsKernelRootComparison.md) and
[`LinearAlgebra/RootDatumZeroFace`](../../LinearAlgebra/RootDatumZeroFace.md).
Throughout, `E = SeparableClosure k`, and base change to `E` is along
`algebraBaseMap k E`.

## Auxiliary results

- `isSplitTorus_baseChange_separableClosure`: every torus over `k` becomes split
  over `E`. This applies the Library theorems `IsTorus.baseChange_of_isAlgebraic`
  and `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites` with the
  published `separablyClosedGroupLikeSpanning`.
- `TitsIndexData.exists_kernelRootEquiv`: assume `IsDerivedSubgroup i` and that
  `D` has affine, locally-finite-type structure morphism. For every actual root
  datum `Q` (index `K`) of the base change to `E` of the inclusion
  `kernelInclusion : T ∩ D ⟶ D`, there is
  `φ₀ : K ≃ {p // (torusMap)_E ≫ P.root p = 0}`, with
  `Q.root q = τ_E ≫ P.root (φ₀ q)` and `Q.coroot q ≫ τ_E = P.coroot (φ₀ q)`.
  Here `P = d.pinning.rootDatum` and `τ = kernelTorusMap : T ∩ D ⟶ T`. This is
  `exists_derivedCentralizerRootEquiv` over `E`. Its geometric inputs are base
  changes of the objects of `TitsKernelTorus`. Connected reductivity of `M_E`
  comes from `connectedReductiveFieldExtensionStatement`, and maximality of the
  tori from `maximalTorusBaseChange`. `i_E` is derived by
  `IsDerivedSubgroup.baseChange_of_eq`. `j_E` represents the centralizer of
  `S_E` by `torusCentralizer_baseChange` and `IsRepresentedBy.baseChange`.
  The split maximal torus `S` stays split (`IsSplitTorus.baseChange`), and
  `T ∩ D` splits by the previous item.
- `characterPrecompInt f` is precomposition with `f` on character lattices, as
  a `ℤ`-linear map. `latticePairing_precomp` states
  `⟨f ≫ χ, ν⟩ = ⟨χ, ν ≫ f⟩` for the actual lattice pairings.

## The coweight `ν` and the zero face

`TitsIndexData.kernelCoweight` is the cocharacter
`ν = (d.positiveCocharacter ≫ d.torusMap)_E` of `T_E`.

- `root'_kernelCoweight`: `P.root' a ν` equals
  `latticePairing S (d.rootRestriction a) d.positiveCocharacter`. The proof
  uses `cocharacterLattice.baseChange_comp`, `latticePairing_precomp`,
  `latticePairing_baseChange`, and the defining base-change equivalence of
  `absoluteRootRestriction`.
- `rootRestriction_eq_zero_iff`: `d.rootRestriction a = 0` exactly when
  `(torusMap)_E ≫ P.root a = 0`.
- `rootRestriction_eq_zero_iff_root'`: `d.rootRestriction a = 0` exactly when
  `P.root' a ν = 0`. The reverse direction uses the field `d.compatible`. If the
  restriction were nonzero with zero pairing, neither `a` nor `-a` would be
  positive (`rootRestriction_neg`), contradicting
  `RootPairing.Base.IsPos.or_neg`.
- `sign_kernelCoweight`: if `P.root' a ν ≠ 0`, then `a` is positive for
  `d.pinning.base` exactly when `0 < P.root' a ν`. This is `d.compatible`.
- `galoisRepresentation_kernelCoweight` and `root'_galoisAction`: `ν` is fixed by
  the Galois action (`cocharacterLattice.galoisRepresentation_baseChange`). So
  the ordinary Galois action `d.pinning.galoisAction σ` preserves every value
  `P.root' a ν` (`IsRootDatumOf.galoisRootIndexEquiv_root` and
  `latticePairing_galoisRepresentation`).

## The reduction theorem

Fix the data of the statement: `k`, `G`, `d`, `j : M ⟶ G` representing the
centralizer of the maximal split torus `S`, and `i : D ⟶ M` with
`IsDerivedSubgroup i`.

1. `D` is semisimple (`kernel_isSemisimple`), so its structure morphism is
   affine and smooth, hence locally of finite type. These are the two instance
   witnesses of the conclusion. `hA` gives `IsAnisotropic D`.
2. `T ∩ D` is a maximal torus of `D` (`isMaximalTorus_kernelInclusion`). Over
   `E`, `D_E` is connected reductive, `(T ∩ D)_E` is split, and its inclusion is
   a maximal torus. The published `rootDatumExistence` gives a finite index type
   `K` and a reduced actual root datum `Q` of this inclusion.
   `exists_kernelRootEquiv` gives `φ₀`.
3. A `FaceDatum P b ν Q` is assembled, with `b = d.pinning.base`. Its fields
   are: `sign` from `sign_kernelCoweight`; `weightMap = characterPrecompInt τ_E`;
   `coweightMap = cocharacterMapInt τ_E`, injective because `τ_E` is a closed
   immersion (`isClosedSubgroup_kernelTorusMap`, `IsClosedSubgroup.baseChange`);
   the adjunction from `latticePairing_precomp`; `indexEquiv` from `φ₀` and
   `rootRestriction_eq_zero_iff_root'`; and the root and coroot laws of `φ₀`.
   Its base `F.base` has support `{q | φ₀ q ∈ d.pinning.base.support}`.
4. The pinning data of `e` over `E` consist of the torus `T ∩ D`, its inclusion
   `kernelInclusion`, the data of step 2, the base `F.base`, and simple-root Lie
   trivializations `RootPinning.ofSplitMaximalTorus`.
5. The split torus of `e` is `TorusExistence.trivialTorus k`, the split torus on
   the empty index type, with inclusion `trivialTorusHom D`, closed because `D`
   is affine. It is a maximal split torus. A factorization through a split
   subtorus `T'` of `D` has `T'` trivial by anisotropy
   (`IsAnisotropic.subsingleton_hom_of_isSplitSubtorus`), so both composites
   with the map back through the trivial group are identities. The torus map is
   `0`. The square holds because maps out of the trivial torus are unique
   (`splitTorus.subsingleton_hom_of_isEmpty`). The positive cocharacter is `0`.
   It is generic because `D` has no relative roots
   (`IsAnisotropic.relativeRoots_eq_empty`). Positivity compatibility is
   vacuous because the character lattice of the trivial torus is trivial.
6. `KernelComparison` uses `τ = kernelTorusMap` and
   `φ : K ≃ {a // d.rootRestriction a = 0}`, obtained from `φ₀` by
   `rootRestriction_eq_zero_iff`. Conjunct 1 is `kernelTorusMap_comp_inclusion`,
   and conjuncts 2 and 3 are the laws of `φ₀`. Conjunct 4 is
   `FaceDatum.pairing_eq` and conjunct 5 is `FaceDatum.mem_base_support`.
7. Conjunct 6, the star action. Fix `σ`. Let `gal` and `gal'` be the ordinary
   Galois actions of `σ` on the root data of `d` and of `e`.
   `GaloisPinningData.exists_weyl_mul_galoisAction_eq_starAction` writes the
   star action of `e` as `w' * gal'` with `w'` in the Weyl group of `Q`, and it
   preserves `F.base.support`. The action `gal` preserves `ν`-values
   (`root'_galoisAction`). It is compatible with the index equivalence:
   `Q.root (gal' q) = σ(Q.root q) = σ(τ_E ≫ P.root (φ q)) = τ_E ≫ P.root (gal (φ q))`.
   The last step is `characterLattice.galoisRepresentation_precompose`, and
   injectivity of `Q.root` identifies `gal (φ q)` with `φ (gal' q)`.
   `FaceDatum.exists_based_correction` gives `w` in the Weyl group of `P` such
   that `w * gal` preserves `d.pinning.base.support` and matches `w' * gal'`
   under `φ`. Both `w * gal` and the star action of `d` are based automorphisms
   in the Weyl coset of `gal`. By `SplitPinning.basedRootDatum_representative_unique`
   and `GaloisPinningData.starAction_mul_galoisAction_inv_mem`, they are equal.
   This gives `φ (star_e(σ) q) = star_d(σ) (φ q)`.

All Library theorems used are published proofs. The module assumes no unproved
statement, and its imports do not reach `LocalRankOneClassificationStatement` or
any local Kneser–Tits statement.
