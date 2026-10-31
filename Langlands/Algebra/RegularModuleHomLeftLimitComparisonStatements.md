# Actual regular-Hom to left-limit comparison statements

Worker 6 authored this statement unit for the whole Renard book program.
Worker 734 checked it against the imported declarations and the source,
and added the two reduced equal-carrier checks described below.

## Source

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.1–I.1.5, printed pp.5–11/PDF11–17, fix
the original nonunital actions and the order on actual idempotents.
Section I.1.4, printed p.9/PDF15, describes the completion of a
nondegenerate module `M` as the families `{m̄(e)}` indexed by the
idempotents `e` of `A`, with `m̄(e) ∈ e·M` and `e·m̄(f) = m̄(e)` for
`e ≤ f`, and maps `m` to the family `m̄(e) = e·m`. The proposition at
I.1.4, printed p.10/PDF16, says that evaluation
`Hom_A(A,M) → M̄, φ ↦ {φ(e)}` is an isomorphism. Its proof notes that
`φ(a) = φ(ae) = aφ(e)` whenever `ae = a`. In the other direction it
reconstructs `φ(a) = a·m̄(e)` for any idempotent `e` with `ae = a`.

The source states this isomorphism before it puts an `A`-module
structure on `M̄`. That structure is defined afterwards by transport
from `Hom_A(A,M)`. So the comparison here is an equivalence of
additive groups.

## The Lean statement

The file imports `Langlands.Algebra.RegularModuleHom` and uses its
declarations by name:

- `RegularModuleHom A M`: the additive maps `φ : A → M` with
  `φ (a * b) = a • φ b`.
- `NonUnitalModuleLeftLimit A M`: the families `x : Idempotent A → M`
  with `e • x e = x e`, and `e • x f = x e` whenever `e ≤ f`. No action
  is installed on this type.
- `RegularModuleHom.toLeftLimit`: evaluation `φ ↦ (e ↦ φ e)`.
- `RegularModuleHom.canonical`: the original-vector intertwiner
  `m ↦ (a ↦ a • m)`.
- `NonUnitalModuleLeftLimit.canonical`: the family `m ↦ (e ↦ e • m)`.

`RegularModuleHomLeftLimitComparison A M` is a `Prop`. It asserts the
existence of an additive equivalence
`E : RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M` with three
properties:

1. `E.toAddMonoidHom = RegularModuleHom.toLeftLimit`. Its forward map
   is the actual evaluation.
2. For every family `x`, every original `a : A` and every actual
   idempotent `e` with `a * e = a`, we have `E.symm x a = a • x.val e`.
3. `E.toAddMonoidHom` composed with
   `RegularModuleHom.canonical.toAddMonoidHom` is exactly
   `NonUnitalModuleLeftLimit.canonical`.

Clause 1 is the source proposition. Clause 2 is the reconstruction
formula from its proof. It is stated at every permitted right unit `e`,
not only at one chosen idempotent. Clause 3 is an explicit
implementation compatibility. The vector `m` gives `a ↦ a • m` as in
formula I.1.5.1, printed p.10/PDF16. Evaluating that map gives the
family `e ↦ e • m` of I.1.4, printed p.9/PDF15. Clauses 2 and 3 are
recorded as conclusions so that later units can use them directly.
Mathematically, both follow from clause 1: clause 2 from the
left-linearity `RegularModuleHom.map_mul_left`, and clause 3 from the
published theorem `RegularModuleHom.toLeftLimit_comp_canonical`. This
file proves neither consequence.

The proposition takes no inverse map, bijectivity certificate, chosen
local unit or comparison equivalence as input. In clause 2, the scalar
action is the specified `NonUnitalModule A M`, through
`NonUnitalModule.actionSMul`, and not some other action on the same
carrier.

## The closed target and its scope

`RegularModuleHomLeftLimitComparisonTheorem` is a closed `Prop`. It
quantifies independently over `A : Type uA` and `M : Type uM`, every
`NonUnitalRing A`, every `AddCommGroup M` and every original
`NonUnitalModule A M`. Its only hypothesis is `IsIdempotented A`.

The source works with a nondegenerate module. This target is an
internal generalization to every original action, and no
`IsNondegenerate A M` hypothesis appears. We include arbitrary actions
because the source's reconstruction needs no fixing idempotent for
target vectors. Right local units for the source scalars and the
compatibility of the family are enough. Two right units `e, e'` of `a`
lie below a common idempotent `f`, which `IsIdempotented A` provides.
Compatibility then gives `a • x e = a • x f = a • x e'`. This statement
does not claim that the original-vector canonical map is injective for a
degenerate action.

No identity, unit-action law, commutativity, nontriviality, countability
or finiteness hypothesis is added. Zero rings, zero actions, trivial
carriers and noncommutative nonunital rings stay within the quantifiers.
When the carriers coincide, the source of `RegularModuleHom` still uses
the ring multiplication, while the target keeps its specified action.

## Checks in the file

- Complete unapplied interfaces at arbitrary independent universes
  `uA, uM` and at both unequal assignments `(0,1)` and `(1,0)`.
- Reflexivity checks that unfold the exact three clauses, and the whole
  closed proposition at `uA, uM`, `(0,1)` and `(1,0)`.
- An equal-carrier specialization with the zero target action
  `NonUnitalModule.zero`, unfolded with that action.
- Two reduced forms of the equal-carrier specialization. With the zero
  target action, clause 2 reads `E.symm x a = 0`. With the regular
  target action `NonUnitalModule.regular A`, it reads
  `E.symm x a = a * x.val e`. Both hold by `rfl`. This shows that the
  formula uses the specified target action and not the ring
  multiplication.

## Not covered

This pair supplies statement coverage only. It proves neither this
comparison nor any completion theorem. The transported original scalar
action on families, the topology and analytic completion, the completion
functor, the nondegenerate-part comparison and the smoothing/completion
adjunction are separate units.
