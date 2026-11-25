# Milne 16.56 from the splitness of the canonical extension

This module serves the proof of
`Langlands.GroupScheme.SplitSolvableSchemeProductStatement` (Milne, *Algebraic Groups* (2017),
Corollary 16.56, printed p.344, source `milne-2017-algebraic-groups`). It derives
the statement from a hypothesis about the extension data (U, D, i, q) that the
statement fixes. The hypothesis says that U is split unipotent and D is a split
torus. In Milne these are two remarks on p.344: "The unipotent subgroup G_u is
split" (proof of Proposition 16.54) and "G/G_u is a split torus" (proof of
Corollary 16.56). A separate module,
[`SplitSolvableCanonicalExtension`](SplitSolvableCanonicalExtension.md), proves
the hypothesis (`SplitSolvableCanonical.canonicalExtension_split`).

Milne's proof of 16.56 runs as follows. G is a G_u-torsor over G/G_u (2.68). The
torsor is trivial by Proposition 16.55(b), because G/G_u is affine and G_u is split
unipotent. G/G_u is a split torus, and G_u ≅ 𝔸^r. The Lean proof follows the same
route. It applies the torsor argument directly to the given i : U ⟶ G and
q : G ⟶ D.

Everything is in the namespace `Langlands.GroupScheme.SplitSolvableScheme`.

## Product

- `nonempty_tensor_iso_of_hasSplitSeries`: let R be a commutative ring, and let
  j : K ⟶ H be a closed subgroup of a group scheme H over Spec R. Let
  q : H ⟶ V be an fppf quotient by range j. Assume H.X is affine over Spec R, V.X
  is an affine scheme, and K has a split series of some length n. Then
  K.X ⊗ V.X ≅ H.X as schemes over Spec R.

  This is the Library lemma `SplitSeriesDecomposition.exists_section_isIso_mul`,
  with "V is a one-dimensional vector group" weakened to "V.X is affine". The
  proof repeats that lemma's argument. Cocycles of K vanish over affine schemes, by
  `SplitUnipotentAffineTorsor.cocyclesVanish_of_hasSplitSeries` (with
  `Cocycle.isTrivial_of_isVectorGroupOfDimension_one` for the one-dimensional
  steps). So `SplitUnipotentAffineTorsor.exists_section` gives a section σ of q.
  This is Milne 16.55(b) for the K-torsor H over V. Then
  `SplitSeriesDecomposition.isIso_mul_of_section` shows that
  (κ, t) ↦ j(κ) · σ(t) is an isomorphism. Its kernel hypotheses come from
  `SplitUnipotentAffineTorsor.comp_comp_eq_one` and
  `SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one`.

## Main theorem

- `nonempty_iso_splitTorus_ulift_fin`: a split torus D over any base scheme S is
  isomorphic to `splitTorus S (ULift (Fin m))` for some m : ℕ. By definition
  (`IsSplitTorus`), D ≅ splitTorus S I for some finite type I. Choose a bijection
  I ≃ Fin m (`Finite.exists_equiv_fin`). The Library isomorphism
  `splitTorus.coordinatePermutationIso` renames the factors along the bijection
  ULift (Fin m) ≃ Fin m ≃ I.

- `splitSolvableSchemeProduct_of_split`: assume the following for every field k,
  every group scheme G over Spec k, every closed subgroup i : U ⟶ G with U
  unipotent, and every fppf quotient q : G ⟶ D by range i with D of
  multiplicative type: if G is split solvable, then U is split unipotent
  (`RelativeRoot.IsSplitUnipotent`) and D is a split torus. Then
  `SplitSolvableSchemeProductStatement` holds.

  Let G be split solvable with data (U, D, i, q) as in the statement. The
  normality hypothesis of the statement is not used. The hypothesis gives a split
  series of U of some length r, and an isomorphism D ≅ splitTorus (Spec k)
  (ULift (Fin m)) by the previous lemma. G is affine over Spec k, and so is its
  closed subgroup U; D is affine because it is of multiplicative type
  (`IsMultiplicativeType.isAffine`). The statement's witnesses are then:

  1. U.X ≅ 𝔸^r: the Library theorem `splitUnipotentAffineSpaceStatement`
     (Milne 14.66), applied to the split series of U.
  2. D ≅ splitTorus (Spec k) (ULift (Fin m)): the isomorphism above.
  3. G.X ≅ 𝔸^r ⊗ T.X, where T = splitTorus (Spec k) (ULift (Fin m)):
     `nonempty_tensor_iso_of_hasSplitSeries` gives U.X ⊗ D.X ≅ G.X. Tensor its
     inverse with the isomorphisms of items 1 and 2 (the second on underlying
     schemes).

The same r serves as the dimension of the affine space for U and as the affine
factor of G, and the same m serves for D and for the torus factor of G, as the
statement requires.
