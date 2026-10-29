# Prime-localization preservation for the actual upper residue-fibre transition

This module defines one proposition,
`Langlands.Algebra.LocalTowerResidueFiberRingBaseChangeStatement`. It is a
statement only. Nothing in this module proves the proposition, and no proof or
witness is assumed. The module defines no new maps or instances. It imports
only the published `Langlands.Algebra.LocalTowerResidueFiberBaseChangeStatement`,
whose ring transition `upperFiberBaseChangeMap` it uses unchanged.

The proposition is exactly the ring implication, the first conjunct, of the
published `Langlands.Algebra.LocalTowerResidueFiberBaseChangeStatement`. It is
isolated so that the ring argument can be proved separately from the module
claim of that statement.

## Setting and notation

The proposition quantifies over all of the following data:

- a nonempty directed preorder `ι : Type uI`;
- commutative local rings `R : Type uR`, `S : Type uS` and `T : Type uT`;
- algebras `R → S`, `S → T` and `R → T` with `IsScalarTower R S T`, where
  `R → S` and `S → T` are local (`IsLocalHom`);
- a synchronized tower `D : LocalAlgebraTowerSystem ι R S T`, with
  components `R_i = D.rs.base i : Type uA`, `S_i = D.rs.alg i : Type uB` and
  `T_i = D.top i : Type uC`;
- indices `i j : ι` with `h : i ≤ j`.

Write `κ_i = ResidueField R_i` and use the published fibre rings

```text
F_i = D.rs.FiberRing i   = S_i ⊗[R_i] κ_i,
G_i = D.UpperFiberRing i = T_i ⊗[R_i] κ_i.
```

`G_i` is an `F_i`-algebra through exactly the published scoped instance
`ResidueFiberTensor.upperAlgebra R_i S_i κ_i T_i`, opened here with
`open scoped ResidueFiberTensor`. Its algebra map is `D.fiberHom i`, given by
`s ⊗ a ↦ algebraMap S_i T_i s ⊗ a`. The published fibre transitions are
`D.rs.fiberRingMap h : F_i →+* F_j` and `D.upperFiberRingMap h : G_i →+* G_j`.

## The map

The map is the published
`LocalAlgebraTowerSystem.upperFiberBaseChangeMap h` of
`LocalTowerResidueFiberBaseChangeStatement`, a ring map

```text
G_i ⊗[F_i] F_j →+* G_j,   g ⊗ f ↦ D.upperFiberRingMap h g * D.fiberHom j f.
```

Here `F_j` is an `F_i`-algebra by the actual lower fibre transition,
`(D.rs.fiberRingMap h).toAlgebra`. The map is `Algebra.TensorProduct.lift` of
the two published maps `D.upperFiberRingMap h` and `D.fiberHom j`. Its
pure-tensor formula is the published simp lemma `upperFiberBaseChangeMap_tmul`,
which holds by `rfl`. It is not an arbitrary isomorphism, algebra structure or
witness field.

## Statement

For all data above, if `D.st.IsPrimeLocalization h` holds, then, with `F_j`
an `F_i`-algebra by `(D.rs.fiberRingMap h).toAlgebra` and `G_j` an algebra
over `G_i ⊗[F_i] F_j` by `(D.upperFiberBaseChangeMap h).toAlgebra`,

```text
∃ (p : Ideal (G_i ⊗[F_i] F_j)) (hp : p.IsPrime),
  IsLocalization.AtPrime G_j p.
```

The hypothesis is the published predicate of the original upper transition:
the map `T_i ⊗[S_i] S_j → T_j`,
`t ⊗ s ↦ D.topMap i j h t * algebraMap S_j T_j s`, is a localization at a
prime.

There are no other hypotheses. In particular there is no assumption of
colimits, approximation, finiteness, flatness, nontriviality, residue
injectivity, tensor invertibility, any other localization property, or
equality of universes. No module data occur, and no fibre transition
conclusion is assumed.

The seven universe parameters `uI`, `uA`, `uB`, `uC`, `uR`, `uS` and `uT`
stay independent. Inspecting the complete declaration reports exactly these
level parameters, in this order, and a `Prop`-valued result.

A private development check, not part of this module, confirmed two facts.
First, the published `LocalTowerResidueFiberBaseChangeStatement` implies this
proposition by taking its first conjunct, with no other change. Second, after
installing `LocalAlgebraTowerSystem.composite_local R S T`, this proposition
yields `D.fiberSystem.IsPrimeLocalization h` of the published package
`Langlands.Algebra.LocalTowerResidueFiberSystem`: the applied proposition
type-checks against that predicate by definitional unfolding alone. The
package is not imported here.

## Provenance

The source is the Stacks Project, Lemma 10.128.8, tag **00R7**, and its proof.
The registered source is `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00R7.html`, lines 224–236 of the snapshot. The registered current check
`stacks-00r7-current-check-2026-10-26` records that the official 00R7 page had
no comments on 26 October 2026 and that the proof's fibre passage is unchanged.
No other errata for this passage were found. The source's upper ring `S'` is
`T` here, and its `𝔭_λ` is the maximal ideal of `R_λ`.

The proof of 00R7 first records, for `λ ≤ μ`, that
`S'_λ ⊗_{S_λ} S_μ → S'_μ` is a localization. This is the hypothesis here. It
then says that, from these transition properties,

```text
S'_λ/𝔭_λS'_λ ⊗_{S_λ/𝔭_λS_λ} S_μ/𝔭_μS_μ → S'_μ/𝔭_μS'_μ   is a localization.
```

The proposition here is the project's version of this displayed map. It is a
derived internal supporting statement; the source does not state it as a
separate lemma. It is isolated from the ring and module conjunction of
`LocalTowerResidueFiberBaseChangeStatement`, which the source also does not
state as a lemma.

The source writes the fibres as quotients by `𝔭_λ`. The published fibre rings
use tensor presentations instead: `S_i ⊗[R_i] κ_i` and `T_i ⊗[R_i] κ_i`. No
quotient-to-tensor comparison is constructed or assumed. The map has the
source's factor order.

The source says only "a localization". Here the conclusion is localization at
a prime ideal, in the same form as the hypothesis `IsPrimeLocalization`. Since
`G_j` is local, the stronger form is expected to follow from localization at
some submonoid. This module does not prove that.

## Expected proof route (not proved here)

Base-change the original localization `T_i ⊗[S_i] S_j → T_j` along
`S_j → F_j`. Identify the source and target with `G_i ⊗[F_i] F_j` and `G_j`
by tensor cancellation, and check that the result is the actual map on pure
tensors. This gives a localization at an image submonoid. Since `G_j` is
local, the submonoid can be enlarged to the complement of the inverse image of
the maximal ideal of `G_j`. None of this is proved here.
