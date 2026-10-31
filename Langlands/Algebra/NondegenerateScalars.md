# Canonical scalars on original nondegenerate modules

This module implements the scalar construction in Renard, *Représentations des
groupes réductifs p-adiques*, version dated 9 July 2026, I.2.1, printed page 14 /
PDF page 20. It starts with the original additive algebra action and constructs
the scalar module on the same additive group. The exact complex case is
`complexModule`; `module` is an internal generalization to a commutative semiring.
All declarations below are in `Langlands.Algebra.NondegenerateScalars`.

## Sources and scope

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, content SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its conventions, printed pages 5–6 / PDF pages 11–12, allow an associative,
possibly noncommutative and nonunital algebra and modules that are abelian groups
with an associative distributive action. I.1.2, printed page 7 / PDF page 13,
provides the idempotented and nondegenerate conditions. I.2.1 gives the unital
scalar formula, its extension to every fixing idempotent, the two compatibility
identities (I.2.1.1), and automatic complex linearity of algebra-module morphisms.
These are the source constructions formalized here. The explicit uniqueness
comparison and the Lean structure/conversion laws are internal consequences and
packaging of those formulas.

The supplementary source is registered as `renard-2010-corrections-complements`,
content SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
PDF pages 18–19 correct the old printed-page-314 theorem by requiring an
additional complex vector-space structure on its module and explaining a
reduction using complex unitization. That concerns modules over an arbitrary
nonunital algebra; it does not supply a prior scalar structure to this
nondegenerate-module construction. The 2026 text governs the present interface.
The relevant original passages and supplementary correction were read directly.

The Hom-space scalar structure, tensor products and unitized Hom/tensor
comparisons later on I.2.1, and the adjunction, exactness and associativity
assertions in I.2.2 / PDF page 21, are outside this module. No category, tensor
object or Hom-space module structure is introduced here.

## Inputs and actual construction

The scalar, algebra and carrier types have independent universes:
`k : Type uK`, `A : Type uA`, `M : Type uM`. The inputs are

```lean
[CommSemiring k] [NonUnitalRing A] [Module k A]
[IsScalarTower k A A] [SMulCommClass k A A]
[AddCommGroup M] [NonUnitalModule A M]
hA : IsIdempotented A
hM : IsNondegenerate A M
```

The two compatibility assumptions express bilinearity of multiplication in `A`:
`(c • a) * b = c • (a * b)` and `a * (c • b) = c • (a * b)`.
Both are explicit parameters of `module`. Neither a prior `Module k M`, a
compatible linear action on `M`, nor a supplied linear-endomorphism realization
is an input. There is no finite-generation, dimension, nontriviality,
commutativity or unit hypothesis on the general algebra/carrier.

`scalarMul k hM c m` chooses an idempotent `e` fixing `m` and returns
`(c • (e : A)) • m`. The outer action is the specified original algebra action.
This raw function is defined before installing a scalar module. For `e ≤ g`
and `e • m = m`, the private helper proves

```text
(c • e) • m = (c • (g * e)) • m
            = (c • g) • (e • m) = (c • g) • m.
```

`fixer_independent` chooses a common upper bound of two fixing idempotents via
`IsIdempotented.finite_upper_bound` and applies that helper twice.
`scalarMul_eq` therefore proves the formula for every fixing idempotent.
The choice is noncomputable, and its value is independent of the choice.

`module k hA hM` is the actual `Module k M` structure whose multiplication is
that raw function. Its laws are proved in the definition. The unit-scalar law
uses the chosen fixer's defining equality. The zero-vector law uses the
original action on zero. Addition of scalars and the zero-scalar law use the
corresponding scalar laws on `A` and additivity of the original action in the
algebra argument. Addition of vectors uses a common upper bound of fixers of
the two summands, with `Idempotent.smul_eq_of_le` making it a simultaneous fixer.
Multiplicative scalar associativity uses `scalarMul_action` to move an outer
scalar through the original action of the scaled fixer, then uses scalar
associativity on `A`. This proof uses no scalar inverses. It works over a
commutative semiring, explaining the internal generalization of the source's
complex construction. Some raw laws need only the scalar-tower half of algebra
bilinearity; the constructed compatible interface retains both hypotheses.

`smul_eq` expresses the all-fixers law using the constructed module:
`c • m = (c • (e : A)) • m` whenever `(e : A) • m = m`.
The additive group and `NonUnitalModule A M` instance are the original inputs.
The module and compatibility adapters are named constructions, installed only
with local declarations; this module defines no global action instances.

## Compatibility and uniqueness

`scalarMul_action` takes a local left unit of `a` from
`IsIdempotented.exists_mem_corner`; it fixes `a • m` and gives
`scalarMul k hM c (a • m) = (c • a) • m`.
`action_scalarMul` instead uses a fixer of `m` and bilinearity on the other side
of multiplication to give `a • scalarMul k hM c m = (c • a) • m`.
Thus `smul_action` and `action_smul` are the two equalities in (I.2.1.1).
`isScalarTower` and `smulCommClass` package these proved laws as named local
adapters.

`toLinearEndHom` installs these adapters locally and calls the published
`NonUnitalModule.toLinearEndHom`. Its result is an actual
`A →ₙₐ[k] Module.End k M`. `toLinearEndHom_apply` states that it evaluates to
`a • m` in the retained original action.

`scalarMul_eq_of_compatible` is a comparison with a preexisting `Module k M`
and `IsScalarTower k A M` on this same group and original action. For a chosen
fixer, the tower identity gives
`(c • e) • m = c • (e • m) = c • m`.
It follows that the constructed raw multiplication agrees with the existing
one. `module_eq_of_compatible` uses `Module.ext'` to identify the actual module
structures. The scalar-tower identity alone suffices for uniqueness, so the
comparison applies in particular when both compatibility laws hold. The prior
module is an input only to these comparison results.

## Automatic linearity and source specializations

For an independently sized `N : Type uN` with its own additive group, original
algebra action and nondegeneracy proof `hN`, `map_scalarMul` starts with any
actual `f : NonUnitalModuleHom A M N`. If `e` fixes `m`, intertwining implies
that `e` also fixes `f m`. Applying the all-fixers formulas on both carriers
and intertwining the algebra element `c • e` proves that `f` preserves the raw
scalars. `map_smul` states this automatic linearity for the constructed modules;
no scalar-linearity proof is supplied by the caller.

`toLinearIntertwiner` reuses the published
`NonUnitalModuleHom.toLinearIntertwiner` with this newly proved linearity.
`ofLinearIntertwiner_toLinearIntertwiner` uses the published forgetting
conversion and recovers the original `f`. `toLinearMap` takes the resulting
actual linear map `M →ₗ[k] N`. Its application and underlying additive-map
laws are `toLinearMap_apply` and `toLinearMap_toAddMonoidHom`; the latter
retains the complete specified additive map. `toLinearMap_id` and
`toLinearMap_comp` give agreement with the original identity and composition.
These packaging equalities are definitional equalities.

For `[Ring R] [Algebra k R]` and an original action with
`hM : IsUnitalModule R M`, `unitalModule` obtains idempotentedness from the unit
and nondegeneracy from the published equivalence with unitality. It constructs
the scalar module without a prior scalar module on `M`. `unital_smul_eq` is the
source formula `c • m = (c • (1 : R)) • m`, obtained by taking the unit idempotent.

`complexModule`, `complex_smul_eq` and `complexToLinearMap` are the exact
specialization to `ℂ`, with algebra and carrier universes still arbitrary and
independent. The algebra can be nonunital and noncommutative; the carriers have
arbitrary dimension. `complexToLinearMap_apply` retains the original function.
Complete unapplied type assignments were checked for both module constructors
and both automatic-linearity maps, including both explicit algebra bilinearity
hypotheses and no prior carrier module or compatibility hypothesis. Development
checks also inspected the construction bodies and the axioms of all public
declarations; only Lean's standard `propext`, `Classical.choice` and `Quot.sound`
appear. These development checks are separate from independent review and
publication.
