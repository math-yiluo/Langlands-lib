# Preservation of the actual residue-module colimit: proof

`Langlands.Algebra.localApproximationResidueModuleColimit` proves the published
proposition `Langlands.Algebra.LocalApproximationResidueModuleColimitStatement`.
Its complete type is exactly that proposition, with the seven independent
universe parameters `uI uA uB uN uR uS uM` in the statement's order. The
statement pair and all of its imports are unchanged. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

The setting is a directed nonempty index preorder `ι`, local rings `R → S`
with a local structure map, a system `D : LocalAlgebraSystem ι R S`, a module
`M` with the caller's compatible `R`- and `S`-actions, and
`E : LocalModuleSystem D M` with `E.IsColimit`. Write `Rᵢ = D.base i`,
`Mᵢ = E.obj i`, `κᵢ` for the residue field of `Rᵢ` and `κ` for the residue
field of `R`. After `letI := Classical.decEq ι`, the theorem shows that the
statement's additive lift

```
AddCommGroup.DirectLimit.lift E.ResidueFiber
  (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom)
  (LocalModuleSystem.TargetResidueFiber R M)
  (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
  (fun _ _ h x ↦ E.residueFiberι_compat h x)
```

from the direct limit of the raw residue modules `κᵢ ⊗[Rᵢ] Mᵢ` to `κ ⊗[R] M`
is bijective. No hypothesis is added. Of `E.IsColimit` the proof uses only
surjectivity of `D.baseColimitMap` and bijectivity of `E.moduleColimitMap`.
Bijectivity of `D.algebraColimitMap` is not used.

## Provenance and relation to the source

The statement's Markdown records the source scope: the observations
`M/𝔪M = colim M_λ/𝔭_λM_λ` in the proof of Stacks Lemma 10.128.8
([00R7](https://stacks.math.columbia.edu/tag/00R7)) and
`M/𝔪M = colim M_λ/𝔪_λM_λ` in the proof of Lemma 10.128.4
([046Y](https://stacks.math.columbia.edu/tag/046Y)), in the registered
original `stacks-algebra-flatness-criteria-2026-10-22`. The source states
these as evident consequences of the ring and module colimits and gives no
argument. The proof below is therefore an internal argument from general facts
about directed colimits and tensor products. It follows the route suggested in
the task contract. It works throughout with the tensor presentation
`κᵢ ⊗[Rᵢ] Mᵢ` of the source quotient `Mᵢ/𝔪ᵢMᵢ` and never forms a quotient.

## Implemented proof

All auxiliary declarations are in the namespace
`Langlands.Algebra.ResidueModuleColimitProof`. They serve only this proof and
introduce no new interface. The proof reuses, from the published namespace
`Langlands.Algebra.ResidueInjectivityProof` (module
`Langlands.Algebra.LocalApproximationResidueInjectivity`), the local instance
`fieldAlgebra`, which makes `κ` an `Rᵢ`-algebra through
`residue R ∘ D.baseι i`, and the following declarations:

- the fixed-field fibres `FieldFiber E i = κ ⊗[Rᵢ] Mᵢ`, their transitions
  `fieldFiberMap` and cocone `fieldFiberι`, which act as the identity on `κ`;
- `exists_fieldFiberMap_eq_zero`: an element of `FieldFiber E i` with zero
  image under `fieldFiberι E i` is killed by some transition
  `fieldFiberMap E h`, given bijectivity of `E.moduleColimitMap` and
  surjectivity of `D.baseColimitMap`;
- `exists_baseι_eq`, `exists_ιM_eq` and `exists_ge_ge`, which represent an
  element of `R` or of `M` at some stage and bound two indices;
- the cancellation isomorphism
  `residueExtensionEquiv E i : κ ⊗[κᵢ] (κᵢ ⊗[Rᵢ] Mᵢ) ≃ κ ⊗[Rᵢ] Mᵢ`,
  its comparison `residueFiberΨ_eq` with the published `E.residueFiberΨ i`,
  and `includeResidue_injective`, the injectivity of `x ↦ 1 ⊗ x` from
  `κᵢ ⊗[Rᵢ] Mᵢ` into `κ ⊗[κᵢ] (κᵢ ⊗[Rᵢ] Mᵢ)`. This holds because a field
  extension is injective and every module over the field `κᵢ` is flat.

**The comparison map.** `residueToField E i` sends a raw residue element
`x : κᵢ ⊗[Rᵢ] Mᵢ` to `residueExtensionEquiv E i (1 ⊗ x)` in
`FieldFiber E i`. The scalar extension uses the algebra structure given by
`D.residueι i : κᵢ → κ`. On pure tensors it is
`b ⊗ m ↦ D.residueι i b ⊗ m` (`residueToField_tmul`). It is additive
(`residueToField_add`, `residueToField_zero`). It is injective
(`residueToField_injective`), as the composite of the injection
`includeResidue_injective` with an isomorphism. It intertwines the published
raw transitions with the fixed-field transitions
(`fieldFiberMap_residueToField`): on pure tensors both sides equal
`D.residueι j (D.residueMap h b) ⊗ E.map i j h m`, by
`LocalAlgebraSystem.residueι_compat`. It also intertwines the published raw
cocone with the fixed-field cocone (`fieldFiberι_residueToField`):
`fieldFiberι E i (residueToField E i x) = E.residueFiberι i x`. This follows
from `residueFiberΨ_eq` and `LocalModuleSystem.residueFiberΨ_tmul` applied to
`1 ⊗ x`.

**Surjectivity** (`lift_surjective`). Induct on an element of `κ ⊗[R] M`.
Sums are handled by adding preimages, since the lift is additive. For a pure
tensor `a ⊗ m`, write `a = residue R r` (`residue_surjective`). Surjectivity
of `D.baseColimitMap` gives `r = D.baseι i r'` (`exists_baseι_eq`), and
surjectivity of `E.moduleColimitMap` gives `m = E.ιM k m'`
(`exists_ιM_eq`). Choose `l ≥ i, k` (`exists_ge_ge`). The element
`residue (D.baseMap i l r') ⊗ E.map k l m'` of the stage-`l` residue module is
then a preimage. The lift sends its image in the direct limit to
`E.residueFiberι l` of it (`AddCommGroup.DirectLimit.lift_of`). That is
`a ⊗ m` by `LocalModuleSystem.residueFiberι_tmul`,
`LocalAlgebraSystem.residueι_residue` and the cocone laws `D.baseι_compat`
and `E.ιM_compat`.

**Injectivity** (`lift_injective`). It suffices that an element of the
direct limit with zero image is zero. By `AddCommGroup.DirectLimit.induction_on`
the element is the image of some `x : κᵢ ⊗[Rᵢ] Mᵢ`, and by `lift_of` its image
is `E.residueFiberι i x = 0`. By `fieldFiberι_residueToField`, the element
`residueToField E i x` of `FieldFiber E i` has zero image under
`fieldFiberι E i`. So `exists_fieldFiberMap_eq_zero` gives `j ≥ i` with
`fieldFiberMap E h (residueToField E i x) = 0`. By
`fieldFiberMap_residueToField` this is
`residueToField E j (E.residueFiberMap h x) = 0`. Since `residueToField E j`
is injective and sends `0` to `0`, `E.residueFiberMap h x = 0`. Hence
the element is zero, because `AddCommGroup.DirectLimit.of_f` identifies the
image of `x` with the image of `E.residueFiberMap h x`.

**Assembly.** `lift_bijective` combines the two halves. The helper theorems
take an arbitrary `[DecidableEq ι]` instance. The final theorem introduces the
statement's binders, sets `let := Classical.decEq ι` to match the statement's
`letI`, and applies `lift_bijective E hE`.
