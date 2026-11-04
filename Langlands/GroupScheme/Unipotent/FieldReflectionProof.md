# Reflection of unipotence under a field extension

Author: Worker 1487.

The theorem `Langlands.GroupScheme.unipotentFieldReflection` has exactly the
type `UnipotentFieldReflectionStatement.{u}`. The associated lemma
`IsUnipotent.of_baseChange` lets unipotence of the actual base change of an
affine group scheme over a field descend to the original group scheme.
The universe is arbitrary, and there is no finite-type, smoothness,
connectedness, characteristic, separability or perfectness assumption.

This proves an intermediate field-extension result. It does not prove the
parent proposition `NoTorusUnipotentStatement`.

## Coordinate descent

`Unipotent.OneMemStable.of_baseChange` proves reflection for the existing
coordinate-bialgebra predicate. Let `V` be a nonzero finite-dimensional
right-translation-stable `k`-subspace of a `k`-bialgebra `B`. Its scalar
extension is represented as the range `W` of the linear map
`K ⊗[k] V → K ⊗[k] B` induced by the inclusion.

Choose a finite basis `b` of `V`. The published
`Chevalley.comul_basis` formula expresses the comultiplication of each
`b j` as `∑ i, b i ⊗ subspaceMatrix V b i j`.
The helper `rightAct_one_tmul_basis` extends this equation to `K` and
contracts the right factor with an arbitrary `K`-linear functional.
The resulting translation of `1 ⊗ b j` is a linear combination of the
same lifted basis vectors. Basis expansion and tensor induction therefore
show that `W` is stable under every right translation over `K`.
It is finite-dimensional because it is a linear-map range of `K ⊗ V`.

Choose a `k`-linear functional `l : K →ₗ[k] k` with `l 1 = 1`.
Contraction of the first tensor factor by `l`, followed by the tensor
unit isomorphism, gives `π : K ⊗ B →ₗ[k] B`.
Every element of `W` contracts into `V`. A nonzero vector `v ∈ V`
gives `1 ⊗ v ∈ W`; if this tensor were zero, contraction would give
`v = 0`. Thus `W` is nonzero.

Applying `OneMemStable` over `K` gives `1 ∈ W`. Contraction then gives
`1 ∈ V`, as required. This argument applies to arbitrary bialgebras over
fields, including coordinate bialgebras without finite type.

## Passage to the group scheme

For an affine group scheme `G`, take its actual coordinate cogroup `C`.
The published `AffineCoordinates.hopfSpecIso` and
`HopfCoordinates.baseChangeSpecIso` identify `G_K` with the Hopf spectrum
of the scalar extension `K ⊗ C`.
The published coordinate-bialgebra equivalence, in the cogroup form
`oneMemStable_of_isUnipotent_cogroup`, transfers the assumed unipotence
of `G_K` to that scalar extension.

Coordinate descent gives `OneMemStable k C`. The reverse cogroup
equivalence, `isUnipotent_cogroup_of_oneMemStable`, then gives
unipotence of the coordinate spectrum. Finally,
`AffineCoordinates.coordinateCogroupIso G` transfers it to `G`.
Both transfers use the published `IsUnipotent.of_iso`, so the conclusion
retains the original fixed-vector equations on every test scheme.

## Provenance

The proof composes the published coordinate constructions with the
linear-algebra argument above. Milne, *Algebraic Groups* (2017),
Corollary 14.9, printed p.282 (one-based PDF p.298), is the classical
finite-type counterpart; its source ID is `milne-2017-algebraic-groups`.
The implemented proof establishes the broader affine scope of the
internal statement directly. It uses no finite-dimensional faithful
representation of `G`.
