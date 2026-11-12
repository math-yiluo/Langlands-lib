# Supplied simply connected covers remain covers after arbitrary field extension

Author: Worker 4036.

The theorem `Langlands.GroupScheme.isSimplyConnectedCover_fieldExtension`
proves exactly the published
`Langlands.GroupScheme.IsSimplyConnectedCoverFieldExtensionStatement.{u}`
from `Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`. Its type
is the bare statement constant, with no added hypotheses.

For an arbitrary universe `u`, fields `k K : Type u` of any characteristic, an
arbitrary `Algebra k K`, `k`-groups `C` and `G`, and every supplied
homomorphism `π : C ⟶ G` with `IsSimplyConnectedCover π`, it proves
`IsSimplyConnectedCover π_K`, where

```lean
π_K = (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map π
```

is the actual pulled-back morphism `C_K ⟶ G_K`. The extension `K/k` may be
transcendental, inseparable or infinite, and the fields may be imperfect.
The theorem is about the given `π`; it does not choose a cover by an existence
theorem.

## Implemented proof

Write `b = Spec.map (CommRingCat.ofHom (algebraMap k K))` and
`F = GroupScheme.baseChange b`. After introducing `k`, `K`, their instances,
`C`, `G`, `π` and `hπ : IsSimplyConnectedCover π`, the proof builds the four
fields of the structure `IsSimplyConnectedCover (F.map π)` from
`Langlands.GroupScheme.SimplyConnected.Basic`, in their declared order.

1. `isSemisimple : IsSemisimple (F.obj G)`. Apply the published theorem
   `isSemisimpleFieldExtension : IsSemisimpleFieldExtensionStatement.{u}`
   (module `Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof`)
   to `k`, `K`, `G` and `hπ.isSemisimple`.
2. `isSimplyConnected : IsSimplyConnected (F.obj C)`. Apply the published
   theorem
   `isSimplyConnectedFieldExtension : IsSimplyConnectedFieldExtensionStatement.{u}`
   (module `Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof`)
   to `k`, `K`, `C` and `hπ.isSimplyConnected`.
3. `isCentralIsogeny : IsCentralIsogeny (F.map π)`. Apply the published
   theorem `centralIsogenyBaseChange : CentralIsogenyBaseChangeStatement.{u}`
   (module `Langlands.GroupScheme.CentralIsogeny.BaseChange`) to the base map
   `b : Spec K ⟶ Spec k`, the groups `C`, `G`, the map `π` and
   `hπ.isCentralIsogeny`. Its conclusion is stated for
   `(GroupScheme.baseChange b).map π`, which is literally `F.map π`. The
   central isogeny predicate keeps the full scheme-theoretic kernel, so this
   step covers non-smooth kernels such as `μ_p` in characteristic `p`.
4. `universal : HasCentralCoverUniversalProperty (F.map π)`. Apply the
   published theorem
   `simplyConnectedCentralCoverUniversalProperty : SimplyConnectedCentralCoverUniversalProperty.{u}`
   (module `Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof`)
   over the field `K` to the groups `F.obj C`, `F.obj G`, the map `F.map π`,
   and the three facts from steps 2, 1 and 3. Its conclusion is the universal
   property over `K`: every central isogeny `q : H ⟶ G_K` from any semisimple
   `K`-group `H`, not only a base change of a `k`-group, has a unique
   `a : C_K ⟶ H` with `a ≫ q = π_K`.

The anonymous constructor `⟨hG, hC, hq, …⟩` assembles these four facts. Nothing
else is used: the proof neither descends a `K`-cover to `k` nor constructs a
comparison between covers.

## Comparing two covers over `K`

If `π' : C' ⟶ G_K` is any other supplied cover over `K`, with
`hπ' : IsSimplyConnectedCover π'`, the comparison isomorphism is the published
`IsSimplyConnectedCover.iso` applied to
`isSimplyConnectedCover_fieldExtension k K C G π hπ` and `hπ'`. It satisfies
`iso_hom_comp` and is unique by `iso_unique`. This module adds no second
comparison.

## Provenance and dependencies

This is a derived assembly of four published Library proofs and the unchanged
definition of `IsSimplyConnectedCover`. They are imported by their Lean
module names. No definition, target statement or imported file is changed.
No `sorry`, `admit` or new axiom is used.

The mathematical source of the statement is recorded in its Markdown:
CGP, *Pseudo-reductive groups*, second edition (2015), source
`conrad-gabber-prasad-2015-pseudo-reductive`, Corollary A.4.11(1), printed
pp.500-501 (PDF pp.526-527), which says the simply connected central cover's
formation commutes with any extension of the base field. The Lean proof
follows the Library interfaces rather than CGP's argument.
