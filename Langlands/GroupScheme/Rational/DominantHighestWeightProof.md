# Proof of dominant highest-weight existence

Author: Worker 1239.

This file proves `Langlands.GroupScheme.SplitDominantHighestWeightRepresentationsExistStatement.{u}`
as the theorem `Langlands.GroupScheme.splitDominantHighestWeightRepresentationsExist`. The
theorem's type is exactly the published proposition. Let `k : Type u` be an algebraically
closed field of any characteristic, `G` an actual affine group scheme over `Spec k`,
`p : SplitPinning G` a split pinning and `lam` an integral torus character with nonnegative
pairing against every simple coroot. The theorem constructs a natural number `n` and an
actual `MatrixRepresentation G (Fin n)` that satisfies the full `p.IsHighestWeight` package
at `lam`. It adds no hypothesis: there is no simple connectedness, no full coroot span and
no representation-existence premise. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

The representation is the finite covariant socle
`Chevalley.affineCovariantSocleRepresentation G f` of a coordinate `f` that realizes `lam`.
`SplitPinning.IsRealizedBy lam f` (module `Reductive.SplitBorelCell`) means three things:

- `f` is left covariant for the extended character of `lam` along the negative Borel
  subgroup;
- `f` is right invariant under the positive unipotent subgroup;
- `f` has counit one.

## Realizing every dominant character

`SplitPinning.exists_pos_nsmul_isRealizedWeight`: every dominant `lam` has some `n > 0`
with `n • lam` realized. It applies
`DominantMultiple.exists_pos_nsmul_mem_realizedSet` (module
`Reductive.DominantMultipleAssembly`) with these inputs:

- the cocharacter `p.positiveCocharacter`. It pairs positively with every simple root,
  because `latticePairing_root_positiveCocharacter_pos_iff` reduces this to positivity of
  the root height, and a simple root has height one;
- `H = p.negativeBorel` with `p.negativeBorelHom` and `p.torusToNegativeBorel`;
- `U = p.positiveUnipotent` with `p.positiveUnipotentHom`, which is unipotent;
- dominance of `lam`, transported through `DominantMultiple.pairing_eq`.

The result is a rational character `χ` of the negative Borel subgroup that restricts to
`n • lam`, together with a coordinate that is covariant for `χ`. `SplitPinning.eq_borelCharacter`
identifies `χ` with the Borel character of `n • lam`. So this coordinate realizes `n • lam`.

`SplitPinning.isRealizedWeight_of_isDominantWeight`: over an algebraically closed field,
every dominant `lam` is realized. This combines the previous lemma with the saturation
theorem `SplitPinning.IsRealizedWeight.of_nsmul` (module `Reductive.SplitBorelCellPower`),
which says that `lam` is realized when some positive multiple of it is.

## The highest-weight package

`SplitPinning.IsRealizedBy.isHighestWeight_affineCovariantSocleRepresentation`: if `f`
realizes `lam`, then the covariant socle of `f` has highest weight `lam`. This lemma holds
over every field. The four components of `IsHighestWeight` are supplied as follows:

1. irreducibility for subspaces stable over every coefficient algebra is
   `IsRealizedBy.isIrreducible` (module `Reductive.SplitBorelCell`);
2. the actual torus character spaces span the representation by
   `SplitPinning.iSup_representationWeightSpace_eq_top` (module
   `MatrixRepresentation.SplitTorusCharacterDecomposition`);
3. the `lam` character space has dimension one by the first component of
   `SplitPinning.affineCovariantSocleRepresentation_weights` (module
   `Reductive.CovariantRegularHighestWeight`);
4. every occurring weight `mu` satisfies `lam - mu ∈ p.positiveRootMonoid`, by the second
   component of the same theorem.

## Assembly

`splitDominantHighestWeightRepresentationsExist` introduces the field, group, pinning and
dominant character, and installs the affine instance on `G` from `IsAffineHom G.X.hom`.
It obtains a realizing coordinate from `isRealizedWeight_of_isDominantWeight`. It then
returns the covariant socle representation with its highest-weight package.

## Provenance

The route is internal. It follows the existence argument of J. S. Milne, *Algebraic Groups*
(2017), Theorem 22.2, printed pp.463–464, which is cited by the statement file. Milne obtains
the representation from regular functions that transform under a Borel subgroup by the given
character. Here these functions are the realizing coordinates. Existence for every dominant
character is proved in two steps: first for a positive multiple, then by saturation, which
uses normality of the coordinate ring. The highest-weight line and the weight bound come from
injectivity of restriction to the positive unipotent subgroup.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
