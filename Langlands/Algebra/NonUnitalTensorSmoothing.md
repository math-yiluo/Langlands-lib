# Tensor smoothing: the inclusion and its balanced reverse

This module constructs the two additive comparison maps in the tensor argument
of David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, I.4.3 "Dualité et complétion", printed page 25 /
PDF31. Worker 1171 authored this Lean/Markdown pair. Unless qualified below,
names are in `Langlands.Algebra.NonUnitalTensorSmoothing`. The module reuses
`Langlands.Algebra.NonUnitalModuleTensor`, the published original balanced
tensor, and the existing `oppositeIdempotent` and `oppositeIdempotent_val`
declarations from `Langlands.Algebra.NonUnitalModuleDualFixedPartMaps`.

The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
passage of I.4.3 beginning "Montrons que le morphisme canonique
ι : N_A ⊗_A M → N ⊗_A M est un isomorphisme" was read in full, along with the
nonunital and nondegenerate conventions of I.1.1–I.1.2 (printed pp. 5–7 /
PDF11–13) and the tensor conventions of I.2.1–I.2.2. As recorded in the task
contract, the parent task checked the registered
`renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), PDF1–2.
The 2026 edition governs.

## Scope and generalization

The source works with a complex algebra `A` with idempotents, a right
`A`-module `N` and a nondegenerate `A`-module `M`. Its argument that `ι` and
`Φ` are well defined uses only the additive groups, the ring multiplication,
the actions and the existence of finite families of local idempotent units.
This module therefore works over an arbitrary associative nonunital ring
`A : Type uA` with `hA : IsIdempotented A`. This is a generalization of the
source hypotheses, not a source assertion.

The right module is an arbitrary `N : Type uN` with its original
`NonUnitalModule Aᵐᵒᵖ N`, and the right action of `a` is `op a • n`. No
nondegeneracy witness, unit law or coefficient-module structure is assumed on
`N`. Only the left module `M : Type uM` with its original `NonUnitalModule A M`
receives a nondegeneracy witness `hM : IsNondegenerate A M`. The universes
`uA`, `uN` and `uM` are independent. No complex `Module` is assumed or installed
on `A`, `N`, `M` or either tensor.

`N_A` is exactly the published `nondegeneratePart hA.op N` with its inherited
original action. Here `hA.op` is the published idempotented structure of the
opposite ring. Both tensors are the published integer-balancing quotients
`NonUnitalModuleTensor.Tensor`, and no replacement tensor object is
introduced.

The source's complex-algebra case is retained without extra assumptions. The
final examples add arbitrary scalar structures over a commutative ring `k`
(for instance `k = ℂ`), namely `Module k A`, `IsScalarTower k A A`,
`SMulCommClass k A A`, `Module k N` and `Module k M`. They show that the
pure-tensor formula for the reverse map applies verbatim. The construction
does not use these structures.

## The inclusion `ι`

`inclusion hA N M : Tensor A N_A M →+ Tensor A N M` is defined as the
published `NonUnitalModuleTensor.map` of precisely the published submodule
inclusion `(nondegeneratePart hA.op N).subtype` and `NonUnitalModuleHom.id A M`.
`inclusion_eq_map` records this equality of entire additive maps. Then
`inclusion_tmul` gives the exact value `ι(n ⊗ m) = (n : N) ⊗ m`, with the
original subtype coercion, on every pure tensor. `inclusion_pure_function` is
the corresponding equality of two-variable functions. All three hold by
definition.

## The smoothed element `n · e`

The reused `NonUnitalModuleDualFixedPartMaps.oppositeIdempotent e` is the
idempotent `op e` of `Aᵐᵒᵖ`, whose action is the right action of `e`. For
`n : N` and any `e : Idempotent A`,
`op_smul_op_smul_self` proves `(n · e) · e = n · e` from the right-module law
`op (a * b) • n = op b • (op a • n)` and `e * e = e`. Then
`smul_mem_nondegeneratePart` proves `op e • n ∈ N_A`, using `oppositeIdempotent e`
as the fixing idempotent. `smoothing hA n e` is the resulting actual element of
`N_A`, and `smoothing_val` gives its original value `op e • n`. The inherited
action of `op e` fixes it (`oppositeIdempotent_smul_smoothing`). Also
`smoothing_zero` and `smoothing_add` give additivity in `n`.

## Choice independence in the actual quotient

`op_smul_smoothing_of_le` shows that for `e ≤ h` the inherited action of `op e`
sends `n · h` to `n · e`. Here the published order gives `h * e = e`, so
`op e • (op h • n) = op (h * e) • n = op e • n`.

`tmul_smoothing_eq_of_le` proves `(n · h) ⊗ m = (n · e) ⊗ m` in the actual
quotient `Tensor A N_A M`, whenever `e ≤ h` and `e · m = m`. The chain is

```text
(n·h) ⊗ m = (n·h) ⊗ (e·m) = ((n·h)·e) ⊗ m = (n·e) ⊗ m,
```

using the published `tmul_balanced` of the quotient over `N_A`, followed by the
previous lemma. Then `tmul_smoothing_eq` takes a common upper bound `h` of any
two fixers `e` and `f` of `m`, using `IsIdempotented.finite_upper_bound`. This
gives `(n · e) ⊗ m = (n · f) ⊗ m`. Upper bounds here are the source's
`he = e, eh = e, hf = f, fh = f`.

The source's displayed chain is
`(n·e)⊗m = (n·e)⊗(h·m) = (n·eh)⊗m = (n·h)⊗m`. Its last step would need
`eh = h`, but `eh = e`. The implemented chain above instead uses `he = e`,
starting from the side of `h`. It proves the source's conclusion that `φ` is
well defined.

## The balanced biadditive map `φ`

`chosenFixer hM m` is the idempotent fixing `m` obtained by choice from the
specified witness `hM m`, and `chosenFixer_smul` is its fixing equation. Then

```text
reverseFun hA N hM n m = (n · chosenFixer hM m) ⊗ m  ∈ Tensor A N_A M.
```

`reverseFun_eq` shows that this value equals `(n · e) ⊗ m` for every
idempotent `e` with `e · m = m`, by `tmul_smoothing_eq`. The particular choice
therefore never matters.

Additivity in `n` follows from `smoothing_add` and the quotient's `add_tmul`.
For additivity in `m`, `reverseFun_add_right` chooses a common upper bound `h`
of the fixers of `m` and `m'`. It fixes `m`, `m'` and `m + m'`
(`Idempotent.smul_eq_of_le`). Rewriting all three values with `reverseFun_eq` at
`h` reduces the claim to `tmul_add`. The zero laws come from `smoothing_zero`,
`zero_tmul` and `tmul_zero`. These proved laws are packaged as the bundled map
`reverseBiadditive hA N hM : N →+ M →+ Tensor A N_A M`. `reverseBiadditive_apply`
and `reverseBiadditive_eq` give its values.

Balancing follows the source's route. For `a : A` and `m : M`,
`exists_fixer_mem_corner` produces an idempotent `h` with `h · m = m`,
`h a = a` and `a h = a`. It takes an upper bound of the chosen fixer of `m`
and a corner idempotent containing `a` (`IsIdempotented.exists_mem_corner`,
`Idempotent.mem_corner_iff`). Then `h` also fixes `a · m`, since
`h · (a · m) = (h a) · m`. Evaluating both sides at `h` reduces
`reverseBiadditive_balanced` to

```text
((n·a)·h) ⊗ m = ((n·h)·a) ⊗ m,
```

after the published `tmul_balanced` moves `a` across in the quotient over
`N_A`. Both smoothed elements have original value `n · (a h) = n · a = n · (h a)`.
This is the source's `φ(n·a, m) = (n·a) ⊗ m = φ(n, a·m)`. The result is a
proof of the published predicate `IsBalanced A (reverseBiadditive hA N hM)`. It
is proved here and is not a hypothesis of any declaration.

## The reverse map `Φ`

`reverse hA N hM : Tensor A N M →+ Tensor A N_A M` is the published
`NonUnitalModuleTensor.lift` of precisely `reverseBiadditive hA N hM` and
`reverseBiadditive_balanced hA N hM`. Its whole lift interface is as follows.

- `reverse_eq_lift`: equality with that lift, as entire additive maps.
- `reverse_comp_projection`: its composite with the published quotient map
  `projection A N M` is the published `integerLift` of `φ`.
- `reverse_tmul_eq_reverseBiadditive` and `reverse_pure_function`: its value
  at `n ⊗ m`, and its two-variable pure-tensor function, are those of `φ`.
- `reverse_unique`: uniqueness among additive maps with these pure-tensor
  values, by the published `lift_unique`.

`reverse_tmul` is the exact pure-tensor formula `Φ(n ⊗ m) = (n · e) ⊗ m` for
every idempotent `e` fixing `m`. `reverse_tmul_independent` derives the
equality of two such values for any two fixers `e` and `f` from this public
formula alone. The value therefore does not depend on the construction's
chosen fixer.

## Degenerate right modules and checks

The `ZeroAction` examples equip an arbitrary group `N`, possibly nonzero, with
the published zero action `NonUnitalModule.zero`. Every smoothed element is
then `0`, and `Φ` vanishes on every pure tensor. A concrete instance uses
`N = ℤ` with the zero right action over `A = ℤ`
(`IsIdempotented.of_ring ℤ`). There `M = ℤ` has the original unital action
`NonUnitalModule.ofModule ℤ ℤ`, whose nondegeneracy is proved in the
preceding example. No nondegeneracy of `N` is assumed or derived.

The section `UniverseChecks` restates every declaration of the construction as
a complete unapplied `∀`-statement and closes it with the declaration itself.
This is done for independent universe variables `(uA, uN, uM)`, and for the
unequal assignments `(0, 1, 0)` and `(1, 0, 1)` in both directions. The ring
and the two carriers therefore remain in independent universes. Neither
carrier universe collapses into the ring's, and no carrier collapses into the
other's.

## Not proved here

The module does not prove `Φ ∘ ι = id` or `ι ∘ Φ = id`, the bijectivity of `ι`,
or any prescribed additive isomorphism or equivalence. It also proves no
naturality in `N` or `M`, no recovered scalar wrappers (a later scalar
successor must use the left-factor-only nondegeneracy API, since `N` may be
degenerate), and no complex-linear equivalence. These are separate successor
units. The parent task retains the comparison of the completion with the full
dual, `M̃ = (M*)_A ≃ M*`, the chain of Hom adjunctions preceding it, the
appeal to A.III.3, and formula (I.4.3.1). None of these is assumed or claimed
here.
