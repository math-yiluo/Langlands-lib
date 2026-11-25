# Injectivity of restriction to the mirabolic subgroup: proof

Lean module: `Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof`.

## Statement

`Langlands.Whittaker.mirabolicRestrictionInjectivity` proves the Library statement
`Langlands.Whittaker.MirabolicRestrictionInjectivityStatement.{uF, uV}`. It is stated in
`Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityStatement`, which this module
imports unchanged. The field universe `uF` and the representation-space universe `uV` are
independent.

```lean
theorem Langlands.Whittaker.mirabolicRestrictionInjectivity :
    MirabolicRestrictionInjectivityStatement.{uF, uV}
```

The statement is the injective half of Jacquet and Shalika 1981, Section (1.1), printed p. 505.
Let `F : Type uF` be a field with instances `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`. Positive characteristic is allowed. Let `n : ℕ`, let
`ψ : UnitaryAdditiveCharacter F`, and let `π` be a representation of
`Langlands.GeneralLinear (n + 1) F` on a complex vector space `V : Type uV` with `IsGeneric ψ n π`.
Then for every `ℓ : glFunctionals ψ n π` with `ℓ.val ≠ 0`, the map
`v ↦ (p ↦ ℓ.val (π p.val v))` from `V` to functions on `mirabolic n F` is injective. The theorem
has no hypotheses beyond those of the statement, and rank one (`n = 0`) is included.

## Proof

The proof is one term. It applies the published reduction to two published theorems.

- `Langlands.Whittaker.mirabolicRestrictionInjectivity_of_multiplicityOne_of_nondegeneracy`,
  in `Langlands.Representation.Whittaker.MirabolicCoefficientKernel`. It takes
  `LocalFieldMultiplicityOneStatement.{uF, uV}` and
  `LocalFieldMirabolicNondegeneracyStatement.{uF, uV}` and gives
  `MirabolicRestrictionInjectivityStatement.{uF, uV}`.
- `Langlands.Whittaker.localFieldMultiplicityOne`, in
  `Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof`. This is
  Whittaker multiplicity one over every nonarchimedean local field.
- `Langlands.Whittaker.localFieldMirabolicNondegeneracy`, in
  `Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyProof`. This is
  Bernstein and Zelevinsky 1977, Theorem 4.9, over every nonarchimedean local
  field. An irreducible generic representation has no nonzero mirabolic subrepresentation whose
  full standard upper-unipotent character quotient vanishes.

The reduction works as follows; its own Markdown has the details. Let `K` be the kernel of the
mirabolic coefficient map `v ↦ (p ↦ ℓ(π(p) v))`. `K` is a mirabolic subrepresentation, and `ℓ`
vanishes on it. Any equivariant functional on `K` extends to `V` by functional exactness. By
multiplicity one, the extension is a scalar multiple of `ℓ`, so it is zero on `K`. Hence the full
character quotient of `K` has zero algebraic dual and is zero. By Theorem 4.9, `K = ⊥`, so the
coefficient map is injective.

All three inputs are stated at the same universes `uF` and `uV` as the target, so they apply
without universe lifting. A Lean check reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
