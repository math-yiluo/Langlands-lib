# Recovery and faithfulness of actual module completion

Authors: Worker 6 and Worker 735. Worker 6 wrote the Lean proof and the
first explanation in a shared draft of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. Worker 735 compiled and inspected
that proof against the current Library. Worker 735 also checked it
against the published target and the original source, and rewrote this
explanation.

This proves the published proposition
`Langlands.Algebra.NonUnitalModuleCompletionRecoveryFaithfulnessTheorem`
from the module `Langlands.Algebra.NonUnitalModuleCompletionRecoveryStatements`.
It is prepared for the exact-target proof task
`50944145-1c14-4d51-bfd5-7b77671e29de`. The closed theorem is
`Langlands.Algebra.nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof`,
and it holds at arbitrary independent universes `uA` and `uM`. The target
and its imported constructions are used by their Lean names without any
change. The proof adds no hypotheses.

## Source

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proposition of I.1.5 is on printed p.10/PDF16. It states that
`(M̄)_A = M` for every `M` in `M(A)`, that the completion functor is
faithful, and that completion is right adjoint to smoothing. The proof
on the same page gives the inclusion (I.1.5.1), `m ↦ φ_m` with
`φ_m(a) = a · m`. It then shows that a `φ` fixed by an idempotent `e`
satisfies `a · φ(e) = φ(a)`. Such a `φ` therefore lies in the image of
(I.1.5.1), which yields (I.1.5.2). On printed p.11/PDF17, Renard argues
that `f̄ = 0` forces `f = 0`, so completion is faithful.

This module proves only the recovery and faithfulness clauses. The
smoothing/completion adjunction, the topological description of the
completion and the submodule closure formula (I.1.5.3) belong to separate
units.

## Recovery of the nondegenerate part

`NonUnitalModuleLeftLimit.partRecovery` proves
`NonUnitalModuleCompletionPartRecovery hA M` from `IsIdempotented A` and
the original `IsNondegenerate A M`. As the target requires, it first
selects the published action `NonUnitalModuleLeftLimit.nonUnitalModule hA`
on the compatible families.

**The map.** The proof restricts the codomain of the published canonical
additive map `NonUnitalModuleLeftLimit.canonical`, `m ↦ (e ↦ e • m)`, to
the actual `nondegeneratePart`. Membership works as follows. Choose an
idempotent `e` with `e • m = m`. The published formula
`NonUnitalModuleLeftLimit.scalarAction_canonical` gives
`e • canonical m = canonical (e • m) = canonical m`, so `e` fixes the
canonical family. Additivity comes directly from additivity of
`canonical`.

**Bijectivity.** Injectivity is the published lemma
`NonUnitalModuleLeftLimit.canonical_injective`. It uses exactly the
original nondegeneracy hypothesis. For surjectivity, let `x` be an
element of the part, fixed by an idempotent `e`. The published identity
`NonUnitalModuleLeftLimit.idempotent_smul` states

```text
e • x.val = canonical (x.val.val e).
```

The left side equals `x.val`, so the vector `x.val.val e` maps to `x`.
This is Renard's argument that a family fixed by `e` comes from the
vector `φ(e)`. `AddEquiv.ofBijective` turns the bijective additive map
into the additive equivalence `E`.

**The conclusions.** The composite of `E` with the actual part inclusion
`(nondegeneratePart hA _).subtype` is the entire map `canonical`. This
holds by definition (`rfl`), because `E` was built by restricting the
codomain of `canonical`. Equivariance `E (a • m) = a • E m` is again
`scalarAction_canonical`, applied after `Subtype.ext`. For the inverse
formula, take any part element `x` and any idempotent `e` with
`e • x.val = x.val`. Then both `canonical (E.symm x)` and
`canonical (x.val.val e)` equal `x.val`. The first holds by
`E.apply_symm_apply`, the second by `idempotent_smul` and the fixing
hypothesis. Canonical injectivity then gives `E.symm x = x.val.val e`.
This argument works for every fixing idempotent, not only for one chosen
idempotent.

The proof never uses the comparison with `Hom_A(A, M)`. Renard states
the proof in terms of `Hom_A(A, M)`, while the target uses compatible
families. The proof works with the families directly and uses the
evaluation step in the same way.

## Faithfulness

`NonUnitalModuleLeftLimit.mapAddHom_injective` proves an internal lemma
that is slightly more general than needed. It assumes a nondegenerate
source `M` and any target `N` with an original action, possibly
degenerate. Under these assumptions,
`NonUnitalModuleLeftLimit.mapAddHom` is injective on original
intertwiners. To compare `f` and `g` at a vector `m`, choose an
idempotent `e` fixing `m`. Evaluate both extended maps at `canonical m`
and take coordinate `e`. Both sides reduce by definition to
`f (e • m) = g (e • m)`, which is `f m = g m`. This is the pointwise form
of Renard's argument that `f̄ = 0` forces `f = 0`. The extra generality
in the target `N` is internal to this proof. It is not a further claim
attributed to the source.

`nondegenerateModuleCompletionFaithful_proof` proves that
`nondegenerateModuleCompletionFunctor.{uA, uM} hA` is `Faithful`. Given
two morphisms of `NondegenerateModuleCat` with equal images, it applies
`ObjectProperty.hom_ext`. Under `NonUnitalModuleHom.toAddMonoidHom`, the
images are the coordinatewise maps of the actual functor. The proof then
applies `mapAddHom_injective` with the source's own nondegeneracy
`M.property`.

`nonUnitalModuleCompletionRecoveryFaithfulnessTheorem_proof` combines
the two results into the closed proposition.

## Checks in the module

- There are complete unapplied type checks of `partRecovery`,
  `nondegenerateModuleCompletionFaithful_proof` and the closed theorem
  at arbitrary `uA, uM`. `mapAddHom_injective` is checked at three
  independent universes `uA, uM, uN`.
- An expanded type check of the closed theorem spells out the selected
  action, the entire canonical-map equality, equivariance, the inverse
  formula for every fixing idempotent, and the actual functor.
- The recovery, faithfulness and closed theorems are checked at the
  universe assignments `(0, 1)` and `(1, 0)`.
- A specialization to the same-carrier zero action
  `NonUnitalModule.zero` on `A` keeps that action and its actual
  `IsNondegenerate` hypothesis.

The proof assumes no unit law, commutativity, nontriviality, field,
countability or dimension hypothesis. Zero rings, zero actions and
trivial carriers stay included. The completion lies in
`Type (max uA uM)` as in the published functor.
