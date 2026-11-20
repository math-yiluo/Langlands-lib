# The unipotent part of an extension of a multiplicative group: reduction to 16.26(a)

Author: Worker 603 (Task 7802). Module
`Langlands.GroupScheme.Unipotent.MultiplicativeExtensionPartReduction`; the
auxiliary declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeExtensionUnipotentPart`.

This module proves the published statement
`MultiplicativeExtensionUnipotentPartStatement` (Milne 16.8, 16.10) from one
premise, the algebraically closed case of Milne's splitting theorem 16.26(a).
Parts 1 and 2 of the statement do not use the premise. The premise itself is
discharged in `MultiplicativeExtensionPartProof` by the theorem
`TrigonalizableExtensionSplit.exists_section_of_isAlgClosed` of
`Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed`.

## The premise

`AlgClosedSplitting.{u} : Prop` says: for every algebraically closed field
`K : Type u`, group scheme `G` over `Spec K` with `[LocallyOfFiniteType G.X.hom]`
and `[IsAffineHom G.X.hom]`, group scheme `U` with `i : U ⟶ G`, finitely
generated additive commutative group `Λ : Type u` and
`q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp`, if
`IsClosedSubgroup i`, `IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal`
and `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, then there is a
group-scheme homomorphism `s` with `s ≫ q = 𝟙 _`. This is exactly case (a) of
the published `TrigonalizableExtensionSplitStatement` (Milne 16.26(a));
`algClosedSplitting_of_trigonalizableExtensionSplit` derives it from that
statement. It is an internal premise of this reduction, not a new target.

## Declarations

- `locallyOfFiniteType_of_isClosedSubgroup`, `isAffineHom_of_isClosedSubgroup`:
  the source of a closed subgroup of a group scheme that is locally of finite
  type (resp. affine) over the base is again so, because the structure map is
  the closed immersion followed by that of the ambient group.
- `range_le_of_isUnipotent`: over a field `k`, let `U` be affine and locally of
  finite type with `IsUnipotent U`, `i : U ⟶ G`, and `q : G ⟶ M` with
  `RelativeRoot.IsFppfQuotient N q` and `IsMultiplicativeType M`. Then
  `SubgroupFunctor.range i ≤ N`.
- `part_one`, `part_two`: the first two conjuncts of the statement, with the
  statement's hypotheses (part 1 needs only that `i` is a closed subgroup of
  the affine finite-type `G` with `U` unipotent).
- `exists_isAlgClosed_diagonalization`: a group of multiplicative type over
  `k` is isomorphic, after base change to some algebraically closed field
  `K ⊇ k` (an algebraic closure of a splitting field), to `D(Λ)` over `K` for a
  finitely generated `Λ`.
- `exists_retraction`: over any base `S`, if `i : U ⟶ G` is a monomorphism,
  `q : G ⟶ Q` has actual kernel range equal to `range i`, and `s ≫ q = 𝟙 Q`,
  then there is a scheme morphism `r : G.X ⟶ U.X` over `S` with
  `i ≫ r = 𝟙`. It need not be a group homomorphism.
- `parts_three_four_of_diagonalization`, `parts_three_four`: the last two
  conjuncts (smoothness and connectedness of `U`), from `AlgClosedSplitting`.
- `Langlands.GroupScheme.multiplicativeExtensionUnipotentPart_of_algClosedSplitting`:
  `AlgClosedSplitting.{u} → MultiplicativeExtensionUnipotentPartStatement.{u}`.
- `Langlands.GroupScheme.multiplicativeExtensionUnipotentPart_of_trigonalizableExtensionSplit`:
  `TrigonalizableExtensionSplitStatement.{u} → MultiplicativeExtensionUnipotentPartStatement.{u}`.

## Proofs

`range_le_of_isUnipotent`. The published proof
`unipotentMultiplicativeTriviality` (Milne 14.16–14.18) gives
`SubgroupFunctor.range (i ≫ q) = ⊥`; its finiteness hypotheses on `M` come
from `IsMultiplicativeType.isAffineHom` and
`IsMultiplicativeType.locallyOfFiniteType`. A point `y ≫ i` of `range i`
therefore satisfies `(y ≫ i) ≫ q = 1`, i.e. it lies in the range of the
actual kernel `kernelι q` (`mem_range_kernelι_iff`), which is `N` by the
last clause of `IsFppfQuotient`.

Part 1. `U` is affine and locally of finite type as a closed subgroup of `G`;
apply `range_le_of_isUnipotent` to `i` and the given `q' : G ⟶ M'`, with
`N = range j`.

Part 2. Let `b : Spec K ⟶ Spec k` and `F` the base-change functor. `F.obj U`
is unipotent by the published `IsUnipotent.baseChange` (Milne 14.9). For a
closed subgroup `j : V ⟶ F.obj G` with `V` unipotent: `F.obj G` is affine and
locally of finite type (base change), hence so is `V`; `F.obj M` is of
multiplicative type (`IsMultiplicativeType.fieldExtension`); and `F.map q` is
an fppf quotient by `range (F.map i)` (`RelativeRoot.IsFppfQuotient.baseChange`
together with `SubgroupFunctor.range_baseChangeHom`). Apply
`range_le_of_isUnipotent` to `j` and `F.map q`.

Parts 3 and 4. Choose `K`, `Λ` and `e : F.obj M ≅ D(Λ)` by
`exists_isAlgClosed_diagonalization` (from the definition of
`IsMultiplicativeType`, an algebraic closure `K` of its splitting field `L`,
`baseChangeFieldTowerIso` and `Diagonalizable.baseChangeIso`). Over `K`, the
base-changed `F.map i` is a closed subgroup (`IsClosedSubgroup.baseChange`),
`F.obj U` is unipotent, the range of `F.map i` is normal
(`SubgroupFunctor.IsNormal.baseChange`), and `F.map q ≫ e.hom` is an fppf
quotient by that range (`IsFppfQuotient.baseChange`, `IsFppfQuotient.comp_iso`).
The premise gives a section `s`. In `exists_retraction`, the point
`g · s(q(g))⁻¹` (the Library's `SplitKernelRetract.adjustment`) of `G_K` on
the universal test scheme `G_K` is killed by the quotient
(`SplitKernelRetract.adjustment_comp`), so it factors as `r ≫ F.map i`; and
`F.map i ≫ r = 𝟙` after cancelling the monomorphism `F.map i`, because points
of `U_K` are killed by the quotient. Thus `U_K` is a scheme retract of `G_K`.
Both are affine schemes (affine over the affine `Spec K`).

- If `G` is smooth, so is `G_K` (base change), and the retract `U_K` is smooth
  by `AffineRetractGeometry.smooth_of_retract` (a retract of a smooth algebra
  over the noetherian `K`). Smoothness descends along the faithfully flat
  quasi-compact `b` (`fieldExtension_fpqc`) by the published
  `smooth_of_baseChange`.
- If `G` is connected, then `G_K` is connected by the published
  `connectedSpace_baseChange_of_connected` (a connected group scheme of finite
  type over a field is geometrically connected), the retract `U_K` is
  connected by `AffineRetractGeometry.connectedSpace_of_retract`, and `U` is
  connected by `connectedSpace_of_baseChange`, since `U_K ⟶ U` is surjective.

The assembled theorems combine the four parts; the second composes the first
with `algClosedSplitting_of_trigonalizableExtensionSplit`.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, printed
pages (PDF page = printed page + 16): Notes 16.8 and 16.10, p.326; Theorem
16.26(a), p.332; Corollary 14.18 and 14.9. The correspondence between the
source and the statement is recorded in the paired Markdown of the published
statement `Langlands/GroupScheme/Unipotent/MultiplicativeExtensionPartStatement.md`.

The route follows Milne's argument for parts 1 and 2 (14.18 forces a
unipotent subgroup into the kernel of every map to a group of multiplicative
type; unipotence and the quotient conditions survive base change). For parts
3 and 4 Milne says that `(G_u)_{k^a}` "becomes a quotient of `G`" by 16.26(a);
the implementation uses the same splitting, over an algebraic closure of a
splitting field of `M` instead of `k^a`, in the form of a scheme retraction
`G_K → U_K` (not a group homomorphism), and then descends smoothness and
connectedness from `K` to `k`. `AlgClosedSplitting` and the auxiliary lemmas
are internal to this derivation.
