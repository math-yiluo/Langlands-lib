# The local restriction formula for induced relative Weil representations

Lean module: `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof`
(namespace `Langlands.ClassField.Global.RelativeWeilGroup`).

Author: Worker 5078.

## Statement

`localInducedRestriction : LocalInducedRestrictionStatement.{uV, u}` proves the published
proposition exactly, with both universes free and no added hypothesis. For every class
family `c` with `FundamentalClass.Restriction c`, every tower `F ⊆ K ⊆ E` of number fields
with `E / F` Galois, every place `w` of `E` above a finite place `z` of `F`, every
reciprocity candidate `e` and every `ι : W_{F_z} → W_{E/F}` with
`IsLocalRelativeWeilMap z w e ι`, it gives `LocalInducedRestriction c F K E h z
(discreteLocalMap ι)`: local maps `W_{K_u} → W_{E/K}` at the places `u` of `K` above
`z` that transfer reciprocity correctly, together with the restriction formula for induced
representations (Tate (1979), (2.3.5) with (1.6.1)).

## Proof

The proof is one application:

`localInducedRestriction_of_extensionSquare LocalClassField.extensionWeilTransferReciprocity.{u, u}`.

- `localInducedRestriction_of_extensionSquare` (published module
  `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionReduction`) proves
  `LocalInducedRestrictionStatement.{uV, u}` from a single hypothesis, the local
  transfer/inclusion square `ExtensionWeilTransferReciprocityStatement.{u, u}`.
- `extensionWeilTransferReciprocity` (module
  `Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof`, part of this
  contribution) proves `ExtensionWeilTransferReciprocityStatement.{u, v}` for all
  universes. Here it is used at `v = u`. Its proof is described in the paired
  Markdown of that module: a normalized common-closure reciprocity family exists, its
  bottom and image-field components are the given geometric candidates by uniqueness,
  and its transfer relation for `⊥ ≤ E` gives the square.

The statement module and the pairs it imports are unchanged.
