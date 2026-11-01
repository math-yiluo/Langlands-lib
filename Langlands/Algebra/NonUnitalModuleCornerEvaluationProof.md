# Image, surjectivity and kernel annihilation for actual corner evaluation

This module proves the unchanged published proposition
`Langlands.Algebra.NonUnitalModuleCornerEvaluationStatement.CornerEvaluationStatement`.
All proof declarations are in
`Langlands.Algebra.NonUnitalModuleCornerEvaluationProof`. The complete type of
the aggregate theorem is

```lean
@cornerEvaluation.{uA, uM} :
  Langlands.Algebra.NonUnitalModuleCornerEvaluationStatement.CornerEvaluationStatement.{uA, uM}
```

There are no term parameters or additional hypotheses on this theorem.
The ring universe `uA` and module universe `uM` remain independent.
The imported statement quantifies over every associative nonunital ring `A`,
idempotent `e : Idempotent A`, and additive commutative group `M` with its
specified original `NonUnitalModule A M` action.

Write `F` for `NonUnitalModuleCorner.FixedPart e M` and `T` for
`NonUnitalModuleCornerInduction.Tensor e F` in this explanation. These
abbreviations do not introduce replacement constructions. The proof uses
exactly the published `fixedPartAddCommGroup`, `fixedPartModule`,
`tensorAddCommGroup` and `tensorModule`, with the original action on `M`.
The source tensor has universe `max uA uM`. The evaluation is the published
original-action intertwiner whose pure-tensor formula is
`evaluation e M (tmul e a z) = a • z.val`.

The three component theorems prove equality of whole original-action
submodule objects, the exact surjectivity criterion, and containment of
whole original-action submodule objects:

```lean
NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M

Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M

NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
  NonUnitalSubmodule.idempotentAnnihilator e T
```

Here `aeM` and `IsGeneratedByIdempotent` are the published definitions in
`NonUnitalModuleIdempotentGenerated`. The annihilator is the published
`NonUnitalSubmodule.idempotentAnnihilator`; its membership condition on `T`
is `∀ a : A, ((e : A) * a) • t = 0` under exactly `tensorModule e F`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original-action conventions are printed pp.5–7 / PDF pp.11–13,
the fixed-part and generatedness definitions are printed p.19 / PDF p.25,
and the relevant evaluation arguments are I.3.2, printed pp.20–22 /
PDF pp.26–28. These passages were read for this proof.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, was also read. Its warnings about the nonunital right corner
action and the annihilator on the source tensor are respected here.
The 2026 text governs statements and numbering. No dedicated Renard errata
note was found in the workspace, current Library or project locations checked.

The full `eA` kernel calculation is explicit on printed p.21 / PDF p.27.
The exact image and surjectivity criterion over arbitrary nonunital rings
are internal generalizations of the source's evaluation calculation for
phi and psi on printed pp.21–22 / PDF pp.27–28. The proof needs neither
the source's later simplicity arguments nor its generated-category closure
argument. It uses additive balanced tensors and the specified original action;
comparison with separately bundled complex scalar structures is outside this
unit.

## Implemented proof

`evaluation_image` proves the two inclusions. For forward containment,
`NonUnitalModuleTensor.projection_surjective` supplies a representative in
the integer tensor product. `TensorProduct.inductionOn` reduces membership
to a pure tensor and addition. A pure tensor evaluates to `a • z.val`;
`fixedPart_le` puts `z.val` in `aeM`, and original-action stability puts
its translate there. Additive closure gives the induction step.
For reverse containment, `aeM_le_iff` reduces to the fixed subgroup.
For any fixed vector `m`, `tmul e e m` evaluates to `m` by
`evaluation_idempotent`. Thus the whole generated submodule lies in the
range.

`evaluation_surjective_iff` unfolds surjectivity as membership of every
vector in the range and rewrites with `evaluation_image`. The resulting
condition is precisely the published `IsGeneratedByIdempotent`.

Three auxiliary identities support the kernel argument.
`tmul_mul_idempotent` balances against the unit of `Idempotent.Corner e`
to show `tmul e (a * e) z = tmul e a z`. This uses the unital corner
action on `F`, without requiring a unit law for the right corner action
on `A`. For `idempotent_smul_tmul`, set `c = e * a * e`, an element of
the corner. Insert the trailing `e` using the first identity, then balance
`c` to the second tensor factor. Since `z` is fixed by `e`, this yields

```text
e • tmul e a z = tmul e e (projection e (a • z.val)).
```

Here `projection e` is the published additive map sending a vector to
its `e`-coordinate in `F`. `idempotent_smul_tensor` compares two additive
maps out of `T`: the action of `e`, and insertion of `e` after projection
of evaluation. `NonUnitalModuleTensor.hom_ext` extends the pure-tensor
identity to every tensor:

```text
e • t = tmul e e (projection e (evaluation e M t)).
```

`evaluation_kernel_le_annihilator` applies this identity when evaluation
vanishes; additivity of projection and the zero pure-tensor law give
`e • t = 0`. The imported
`NonUnitalSubmodule.le_idempotentAnnihilator_iff` upgrades this to the
full claimed containment: the kernel is stable under the original
`A`-action, so applying `e`-annihilation to `a • t` and using action
associativity gives `((e : A) * a) • t = 0` for every `a`.
Finally, `cornerEvaluation` assembles the three component proofs in the
published conjunction order.

## Interface and boundary checks

The `Checks` namespace contains reproducible complete-type assignments
for the aggregate at arbitrary independent universes and at `(0,1)` and
`(1,0)`, and complete quantified types for the three component theorems.
Named-action examples explicitly select an original action `h₀` in the
presence of a competing instance `h₁`, listing the inherited fixed-part
and source tensor structures in the range and kernel expressions. The
pointwise kernel example obtains the full `e*a` conclusion under that
same named tensor action.

The zero-idempotent and explicitly specified zero-action examples derive
surjectivity exactly when every vector is zero, using the published
generatedness criteria. Subsingleton module and ring examples specialize
all three conclusions. These examples use the proved results directly.
The proof imposes no unitality, idempotentedness, nondegeneracy,
generatedness, simplicity, nonzero-carrier, finite-dimensionality or
commutativity premise. Kernel equality, fixed-part induction isomorphisms,
generated-category closure, equivalences and adjunctions remain separate.
