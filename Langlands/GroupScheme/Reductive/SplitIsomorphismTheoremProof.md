# Proof: the Isomorphism Theorem for split reductive groups

Author: Worker 74. The route follows the outline of an earlier compiled draft by
Worker 3483 (program Task 3483), as described in this task's context. That draft was
not available in this instance, so this file was written independently from the outline.

This module proves the published proposition
`Langlands.GroupScheme.SplitIsomorphismTheoremStatement`
([`Reductive.SplitIsomorphismTheoremStatement`](SplitIsomorphismTheoremStatement.md)) at
its published universe `u`. Let `k` be a field, `G` and `G'` connected reductive groups
over `Spec k`, `i : T ⟶ G` and `i' : T' ⟶ G'` split maximal tori, `P` and `P'` root data
of `i` and `i'`, and `f : RootPairing.Equiv P' P` an equivalence of root pairings. Then
there are `φ : G ≅ G'` and `t : T ≅ T'` with `i ≫ φ.hom = t.hom ≫ i'` and
`f.weightMap χ = t.hom ≫ χ` for every character `χ` of `T'`. This is the existence part
of the Isomorphism Theorem (Milne, *Algebraic Groups* (2017), Theorem 23.25 in its
"isomorphism" form, and Remark 23.26). The module proves nothing beyond that statement,
adds no hypothesis and no axioms.

## Declaration

- `splitIsomorphismTheorem : SplitIsomorphismTheoremStatement.{u}`, the only
  declaration of the module. It depends on `propext`, `Classical.choice` and
  `Quot.sound` only.

The module uses no non-default options.

## Proof

The proof reduces the target to the Isomorphism Theorem for a common split maximal
torus. It replaces `i'` by its precomposition with a torus isomorphism `T ≅ T'` that
realizes the weight map of `f`. The steps of the Lean proof are as follows.

1. **Instances.** `IsRootDatumOf` needs `IsAffineHom` for the structure maps of `G`
   and `G'`. The proof takes them from the reductivity proofs, `hG.isAffineHom` and
   `hG'.isAffineHom`, as the statement does.

2. **The torus isomorphism.** Let
   `s : T' ≅ T := hT'.isoOfCharacterEquiv hT f.weightEquiv.toAddEquiv`, the isomorphism
   of split tori whose character pullback realizes the bijective weight map of `f`. By
   `IsSplitTorus.character_congr_isoOfCharacterEquiv`,
   `characterLattice.congr s = f.weightEquiv.toAddEquiv`. Since
   `characterLattice.congr s χ = s.inv ≫ χ` by definition, this says
   `s.inv ≫ χ = f.weightMap χ` for every `χ : characterLattice T'` (`hs`).

3. **The inverse equivalence.** Let `e := RootPairing.Equiv.symm P' P f : P ≃ P'`. Its
   weight map is `f.weightEquiv.symm` by definition. For every `χ : characterLattice T`
   the proof shows `e.weightEquiv χ = characterLattice.congr s.symm χ = s.hom ≫ χ`
   (`he`). It applies the injective map `f.weightEquiv` to both sides. The left side
   becomes `χ` by `LinearEquiv.apply_symm_apply`. The right side becomes
   `s.inv ≫ s.hom ≫ χ` by `hs` and `characterLattice.congr_apply`, which is `χ` by
   `Iso.inv_hom_id_assoc`.

4. **Transport of the second root datum.** `IsRootDatumOf.precomp_torusIso` takes the
   isomorphism `s.symm : T ≅ T'`, the hypothesis `IsRootDatumOf i' P'`, the pairing
   component `hP.1 : P.toLinearMap = latticePairing T` of `IsRootDatumOf i P`, the
   equivalence `e` and `he`. It gives
   `IsRootDatumOf (CommGroupScheme.groupHom s.symm.hom ≫ i') P` (`hR`). So `P` is also a
   root datum of the torus `T` embedded into `G'` through `s.symm` and `i'`.
   `IsMaximalTorus.precomp_torusIso` applied to `s.symm` and `IsMaximalTorus i'` shows
   that this composite is a maximal torus of `G'` (`hM`).

5. **The common-torus Isomorphism Theorem.** `splitCommonTorusIsomorphism` is applied
   to `k`, `G`, `G'`, `hG`, `hG'`, the common split torus `T` with `hT`, the embeddings
   `i` and `CommGroupScheme.groupHom s.symm.hom ≫ i'`, `hi` and `hM`, the index types
   `J`, `J`, the root data `P`, `P` with `hP` and `hR`, and the reindexing
   `Equiv.refl J`. The root and coroot conditions hold by `rfl`. It gives
   `φ : G ≅ G'` with `i ≫ φ.hom = CommGroupScheme.groupHom s.symm.hom ≫ i'`.

6. **Conclusion.** Take `φ` and `t := s.symm`. The first equation is the result of
   step 5. For the second, `t.hom = s.inv`, so `f.weightMap χ = t.hom ≫ χ` is `hs`
   at `χ`, read backwards.

## Published inputs

From the Library:

- `Langlands.GroupScheme.IsSplitTorus.isoOfCharacterEquiv` (definition) and
  `Langlands.GroupScheme.IsSplitTorus.character_congr_isoOfCharacterEquiv`, module
  `Langlands.GroupScheme.Reductive.PinningLattice`
  ([`Reductive.PinningLattice`](PinningLattice.md)).
- `Langlands.GroupScheme.characterLattice.congr` (definition) and
  `Langlands.GroupScheme.characterLattice.congr_apply`, module
  `Langlands.GroupScheme.Torus.LatticeGalois`
  ([`Torus.LatticeGalois`](../Torus/LatticeGalois.md)).
- `Langlands.GroupScheme.IsRootDatumOf.precomp_torusIso` and
  `Langlands.GroupScheme.IsMaximalTorus.precomp_torusIso`, module
  `Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction`
  ([`Reductive.PinnedIsomorphismReduction`](PinnedIsomorphismReduction.md)).
- `Langlands.GroupScheme.splitCommonTorusIsomorphism :
  SplitCommonTorusIsomorphismStatement.{u}`, module
  `Langlands.GroupScheme.Reductive.SplitIsomorphismProof`
  ([`Reductive.SplitIsomorphismProof`](SplitIsomorphismProof.md)). This is the
  Isomorphism Theorem for a common split maximal torus and the identity of the
  character lattice.
- The structure field `Langlands.GroupScheme.IsConnectedReductive.isAffineHom`, module
  `Langlands.GroupScheme.Reductive.Basic` ([`Reductive.Basic`](Basic.md)).

From Mathlib: `RootPairing.Equiv.symm` and `RootPairing.Equiv.weightEquiv`
(`Mathlib.LinearAlgebra.RootSystem.Hom`), `LinearEquiv.apply_symm_apply`,
`CategoryTheory.Iso.symm` and `CategoryTheory.Iso.inv_hom_id_assoc`.

## Imports

The module imports the target's statement module
`Langlands.GroupScheme.Reductive.SplitIsomorphismTheoremStatement` and the published
modules `Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction` (which imports
`Reductive.PinningLattice`) and `Langlands.GroupScheme.Reductive.SplitIsomorphismProof`.
It does not change the statement's Lean/Markdown pair or anything it imports.

## Relation to the source

Milne obtains Remark 23.26 from the Isogeny Theorem 23.25, whose proof combines 23.5,
23.6, 23.7 and 23.9. The Lean proof does not follow that route. It uses the published
common-torus case, which carries the substantial content, and reduces the general case
to it by transporting the root datum along a torus isomorphism. The uniqueness part of
Remark 23.26 is not part of the target and is not proved here.
