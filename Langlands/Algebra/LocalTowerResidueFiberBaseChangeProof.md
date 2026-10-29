# Canonical residue-fibre transition localization and module base change: proof

`Langlands.Algebra.localTowerResidueFiberBaseChange` proves exactly
`Langlands.Algebra.LocalTowerResidueFiberBaseChangeStatement`, with its nine
independent universe parameters `uI uA uB uC uN uR uS uT uM`. For every local
algebra tower `D` over a nonempty directed preorder, the actual upper
residue-fibre ring transition preserves prime localization, and the actual
upper residue-fibre module transition preserves bijectivity. Each implication
uses only its own transition hypothesis.

The module imports
`Langlands.Algebra.LocalTowerResidueFiberRingBaseChange`. The statement pair
and its imports are unchanged. The ambient rings and module retain all the
structures in the statement.

Write `R_i = D.rs.base i`, `S_i = D.rs.alg i`, `T_i = D.top i`,
`κ_i = ResidueField R_i`, `F_i = S_i ⊗[R_i] κ_i`, and
`G_i = T_i ⊗[R_i] κ_i`. For `E : LocalModuleTowerSystem D M`, write
`M_i = E.stModule.obj i` and `N_i = E.rsModule.ResidueFiber i`.

## Ring implication

The first conjunct is the published theorem
`Langlands.Algebra.localTowerResidueFiberRingBaseChange`, applied to the same
`ι`, `R`, `S`, `T`, and `D`. It proves localization at a prime for the actual
map `D.upperFiberBaseChangeMap h : G_i ⊗[F_i] F_j →+* G_j`, using the lower
transition algebra `(D.rs.fiberRingMap h).toAlgebra` and the published
`ResidueFiberTensor.upperAlgebra`.

That imported proof identifies the actual fibre transition as the base change
of `D.st.ringBaseChangeMap h` by pasting pushout squares and checking the maps
on generators. Localization survives this base change. The published locality
of `G_j` then gives localization at the inverse image of its maximal ideal.
Its hypothesis is only `D.st.IsPrimeLocalization h`.

## Module implication

`LocalModuleTowerSystem.upperResidueFiberBaseChangeMap_bijective` proves the
second implication independently of any ring localization. Fix `h : i ≤ j`
and assume bijectivity of `E.stModule.moduleBaseChangeMap h`.
Put `A = T_i`, `B = T_j`, `C = G_i`, and `Q = G_j`.

The proof uses the actual transition maps to install the compatible algebras
`A → B → Q` and `A → C → Q`. Compatibility of the second tower is checked by
tensor induction using `upperFiberRingMap_tmul`. Tensor cancellation also
needs an explicitly stated mixed scalar tower on `Q`: the algebra action
through `A → Q` on the intermediate ring agrees with the existing tensor
action on the final module `Q`. Tensor induction proves this agreement.
The published `B`-action on `Q` is retained.

The proof constructs the following composite linear equivalence:

```text
Q ⊗[C] N_i
  ≃ Q ⊗[C] (C ⊗[A] M_i)
  ≃ Q ⊗[A] M_i
  ≃ Q ⊗[B] (B ⊗[A] M_i)
  ≃ Q ⊗[B] M_j
  ≃ N_j.
```

The first arrow base-changes the inverse of the published
`E.upperFiberModuleEquiv i`. The next two arrows are Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange` and the inverse of
another instance of that equivalence. The fourth arrow base-changes
`LinearEquiv.ofBijective (E.stModule.moduleBaseChangeMap h) hbij` along
`B → Q`. The last arrow is `E.upperFiberModuleEquiv j`.

The linear map underlying this composite is proved equal to the actual
`E.upperResidueFiberBaseChangeMap h`. Linear-map extensionality and tensor
induction reduce the equality to a pure tensor
`(t ⊗ b) ⊗ (a ⊗ m)`. The proof expands base change, tensor cancellation,
`upperFiberModuleEquiv_symm_tmul`, and the original module transition. The
published formulas for the upper fibre comparison and transition then
identify both sides. In particular, the target map has the prescribed formula
`g ⊗ n ↦ g • E.rsModule.residueFiberMap h n`.

All residue modules retain the published `ResidueFiberTensor.rawModule`
action. The map being proved bijective is exactly the statement's map with
its restricted `Module.compHom` action; the proof does not route through a
module package requiring a compatible ambient `R`-action on `M`.
Bijectivity follows from the composite equivalence and the proved equality.

The final theorem introduces the ring data and `D`, pairs the imported ring
implication with this module lemma, and adds no binders or hypotheses to the
published proposition.

## Provenance

This is an internal derived tensor argument for the two fibre-transition
assertions in the proof of Stacks Project Lemma 10.128.8, tag **00R7**.
The registered source is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00R7.html`, snapshot lines 224–236. Line 224 records the original upper
transition localization and module isomorphism; lines 227–236 assert the
corresponding properties after passage to quotient fibres.

The published statement expresses the fibres by tensors and places the scalar
factor first in the module tensor. This proof follows those conventions and
checks the actual published maps. The module argument supplies tensor
cancellation details that the source leaves implicit. The ring proof's
prime-localization conclusion strengthens the source's localization assertion
using the local target, as explained in its companion Markdown.
