# Central quotient and coefficient transport

Author: Worker 84. Provenance: internal.

This module derives transport constructions from
`Langlands.Representation.MatrixCoefficient.ModuloCenter` and Mathlib's actual
group centers and quotient groups. It introduces no new quotient model or
transport hypothesis.

The group types `G : Type uG` and `H : Type uH`, and complex module
`V : Type uV`, have independent universes. Fix group structures and topologies
on `G` and `H`, a continuous multiplicative equivalence `e : H ≃ₜ* G`, and
`ρ : Representation ℂ G V`. These constructions work in particular for
topological groups; they do not need continuity of the group operations.
The carrier `V` has only an additive commutative group and complex module
structure. There is no topology, dimension, smoothness, admissibility,
irreducibility, or unitarizability assumption on it or its representation.

## Actual central quotient

`Langlands.centralQuotientCongr e` has type
`(H ⧸ Subgroup.center H) ≃ₜ* (G ⧸ Subgroup.center G)`.
Its multiplicative equivalence is Mathlib's `QuotientGroup.congr`, using
`Subgroup.map_center_eq` to identify the image of the actual center. The
forward function sends the class of `h` to the class of `e h`, as expressed
by `centralQuotientCongr_mk`. The inverse sends the class of `g` to the
class of `e.symm g`. The inverse identities and multiplicativity come from
the algebraic quotient equivalence. `centralQuotientCongr_symm` identifies
this inverse with `centralQuotientCongr e.symm`.

Both continuities are proved using the quotient topology: precomposition
with the corresponding quotient projection gives the continuous composite
of `e` (respectively `e.symm`) with the other quotient projection. No
closedness, separation, compactness, or measurable structure is required.

## Central character and descended norm

For `c : UnitaryCentralCharacter ρ`,
`Langlands.UnitaryCentralCharacter.compContinuousMulEquiv c e` has type
`UnitaryCentralCharacter (ρ.comp e.toMonoidHom)`. The action is on the same
carrier `V`. Its character is the composite of `c.character` with
`(Subgroup.centerCongr e.toMulEquiv).toMonoidHom`. This actual center
restriction sends `z` to the center element with underlying value `e z`;
`compContinuousMulEquiv_character` gives the character's pointwise formula.

The center restriction is continuous for the subgroup topologies, by
continuity of the inclusion, of `e`, and the subtype construction. The
new character kernel is the preimage of the old kernel, so it is open.
Norm-one values follow from `c.norm_eq_one` at the image center element.
The scalar-action proof is `c.acts` at that same element and the unchanged
vector.

`Langlands.UnitaryCentralCharacter.coefficientNorm_compContinuousMulEquiv`
proves, for every algebraic functional `ℓ : Module.Dual ℂ V` and `v : V`,

```text
(c.compContinuousMulEquiv e).coefficientNorm ℓ v
  = c.coefficientNorm ℓ v ∘ centralQuotientCongr e.
```

The proof is function extensionality followed by quotient induction.
On a representative `h`, both sides reduce to `‖ℓ (ρ (e h) v)‖`.
It uses the existing descended coefficient norm, whose well-definedness
comes from the unitary scalar action.

## Scope and provenance

These are internal constructions and defining laws derived from the imported
definitions, rather than transcriptions of an external theorem. No external
literature is used. The module supplies no smooth-dual, admissibility,
Haar-measure, `MemLp`, temperedness, or square-integrability transport theorem.
Those analytic applications can use the quotient equivalence and coefficient
identity without changing the existing analytic predicates.
