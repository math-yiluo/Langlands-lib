# Local transfer reciprocity for local relative Weil maps

Lean module: `Langlands.ClassField.Global.LocalRelativeWeilTransferProof`
(namespace `Langlands.ClassField.Global.RelativeWeilGroup`).

Author: Worker 5086, using the reduction drafted by Worker 1835 (see the companion
module).

## Statement proved

`localTransferReciprocity : LocalTransferReciprocityStatement.{u}`

This proves exactly the published proposition
`Langlands.ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement.{u}`
of the module `Langlands.ClassField.Global.LocalRelativeWeilTransferStatement`, for an
arbitrary universe `u`. For every class family `c : FundamentalClass.ClassFamily.{u}`,
all number fields `F E : Type u` with `[Algebra F E]` and `[IsGalois F E]`, every finite
place `z` of `F`, every finite place `w` of `E` with `[w.asIdeal.LiesOver z.asIdeal]`,
every reciprocity candidate `e` of `E_w = towerPadicField z w` and every
`ι : W_{F_z} →ₜ* W_{E/F}` with `IsLocalRelativeWeilMap z w e ι`, it gives
`HasLocalTransferReciprocity z ι`. That is: for every geometric reciprocity candidate
`ez` of `F_z = padicField z` and every `g ∈ W_{F_z}`,
`transfer c F E (ι g) = ([ez(g)]_z)⁻¹` in `C_F`, where `[a]_z` is
`IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a`.

The theorem adds no hypothesis. In particular it assumes no arithmetic property of the
class family `c` (`IsArithmeticClassFamily`, `FundamentalClass.Restriction`, and so on),
no transfer reciprocity for `W_{E/F}`, and no existence or conjugacy statement for local
maps. The statement module and the pairs it imports are unchanged.

This is the relative form, for `E = F` in Tate's notation, of Proposition (1.6.1) of
John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
p.8. The target Markdown, "Relation to the source", lists the differences.

## Proof

The proof is one line:

`localTransferReciprocity_of_square LocalClassField.extensionWeilTransferReciprocity.{u, u}`.

1. `localTransferReciprocity_of_square`, in the companion module
   `Langlands.ClassField.Global.LocalRelativeWeilTransferReduction` (submitted with this
   proof), proves `LocalTransferReciprocityStatement.{u}` from
   `LocalClassField.ExtensionWeilTransferReciprocityStatement.{u, u}`. That is the local
   transfer/inclusion square of Jean-Pierre Serre, *Local Fields*, GTM 67 (1979), Chap.
   XI, §3, diagram (2), p.170: for an embedding `f : F' → E'` of p-adic fields, the
   transfer `W_{F'} → W_{E'}^{ab}`, read in `E'ˣ` through a geometric reciprocity map of
   `E'`, equals geometric reciprocity of `F'` followed by `f`. The reduction applies it to
   `F' = padicField z`, `E' = towerPadicField z w` and
   `f = completionPadicAlgHom z w`. Its Markdown gives the full argument:
   - the image of `W_{F_z}` in `Gal(E/F)` is the decomposition group `D_w`;
   - the preimage under `ι` of `C_E` is the image of `W_{E_w}`;
   - the transfer `W_{E/F} → C_E` of `ι g` is a product, over representatives of
     `Gal(E/F)/D_w`, of Galois conjugates of the inverse of the local transfer read
     through `e`;
   - that product is the image in `C_E` of `([a]_z)⁻¹`, where `a ∈ F_zˣ` has the local
     transfer as its image in `E_wˣ`.

   All of this holds for an arbitrary class family `c`.
2. `Langlands.LocalClassField.extensionWeilTransferReciprocity :
   ExtensionWeilTransferReciprocityStatement.{u, v}` (module
   `Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof`) is the published
   unconditional proof of the square, here at universes `{u, u}`.

The kernel check of `localTransferReciprocity` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Dependencies and circularity

The proof uses only published theorems, and it takes none of the following as a
hypothesis or uses a proof of it:

- `Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`;
- the Hecke functional equation;
- `LocalInducedRestrictionStatement`;
- `RelativeWeilTransferReciprocityStatement` or its proof `relativeWeilTransferReciprocity`;
- local Langlands results.

The import closure contains the module
`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement`, which
defines `LocalInducedRestrictionStatement`. It comes in through the imports of the
published square proof (`Langlands.Global.Factors.RelativeWeilLocalEpsilon`). No module
that proves one of the statements listed above is in the import closure.

As a private development check, the author traversed all constants that
`localTransferReciprocity` uses, directly or indirectly. No constant name contains
`FunctionalEquation`, `LocalInducedRestriction`, `RelativeWeilTransferReciprocity`,
`RelativeWeilLocalRestriction`, `Hecke` or `Supercuspidal`. The only
`Langlands.Correspondence` constants used are rank-one local class field theory
results that the published square proof needs: the base reciprocity candidate
`baseReciprocityCandidate` and its specification, `baseWeilEquiv`, and the
norm-residue and geometric-residue lemmas behind them.

## Public theorems used

- `Langlands.ClassField.Global.RelativeWeilGroup.localTransferReciprocity_of_square`
  (companion module `LocalRelativeWeilTransferReduction`; that module's Markdown lists
  the published results it uses, among them
  `Langlands.GroupTheory.Transfer.transfer_comp_eq_prod_of_normal` and
  `Langlands.ClassField.Global.prod_relativeIdeleClassAut_ofAdicCompletion_of_coset`).
- `Langlands.LocalClassField.extensionWeilTransferReciprocity`.
