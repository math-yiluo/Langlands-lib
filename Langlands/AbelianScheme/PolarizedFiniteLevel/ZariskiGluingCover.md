# The locally directed cover by opens contained in a member of an open cover

Helper module for gluing ordinary polarized full-level data along an open cover
(used by `ModuliZariskiSheafOfRigidityProof`, which derives the Zariski sheaf property from rigidity). It turns an arbitrary open cover `U : ι → S.Opens` of a scheme `S` into
a *locally directed* open cover, as required by Mathlib's relative gluing
(`Scheme.Cover.RelativeGluingData`, Stacks Tag 01LH).

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`.

- `SubOpens U`: the opens `W` of `S` with `W ≤ U i` for some `i`, ordered by inclusion
  (`PartialOrder`).
- `isOpenCover_subOpens hU`: if `iSup U = ⊤`, the family `W ↦ W` indexed by `SubOpens U`
  is an open cover.
- `subCover hU : S.OpenCover`: the open cover of `S` by the inclusions `W.ι` of these
  opens (Mathlib's `Scheme.openCoverOfIsOpenCover`).
- Instances on `(subCover hU).I₀`: the partial order, `LocallyDirected`, `Small.{u}` and
  `Quiver.IsThin`.
- `subCover_le_iff`: `W ≤ W'` iff the images (`opensRange`) are nested.
- `subCover_isBasis`: these images form a basis of the topology of `S`.
- `subCover_trans`: the transition map of the locally directed cover along `W ≤ W'` is
  `S.homOfLE`.

## Proofs

`isOpenCover_subOpens`: every point lies in some `U i`, and `U i` itself belongs to the
family. `subCover_isBasis`: for an open `V` and `x ∈ V`, choose `i` with `x ∈ U i`; then
`V ⊓ U i` is in the family, contains `x` and lies in `V`. The `LocallyDirected` instance
is Mathlib's `Cover.LocallyDirected.ofIsBasisOpensRange` applied to these two facts.
`subCover_trans`: both sides composed with the monomorphism `W'.ι` give `W.ι`
(`Scheme.Cover.trans_map`, `Scheme.homOfLE_ι`).

## Provenance

Internal. The reduction from arbitrary covers to locally directed ones (opens below
some member form a basis) is standard; Mathlib supplies the locally directed
machinery.
