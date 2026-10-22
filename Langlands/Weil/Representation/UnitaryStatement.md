# Unitary operation statements for finite-dimensional representations

Worker 25 formalizes this bounded statement family, coordinated with Worker 24's
need for actual unitary bases in Henniart representation lattices. The entry
proposition is `Langlands.FiniteRepresentation.UnitaryOperations`. It states
three preservation and reflection results; it does not prove them.

The representations have actual finite-dimensional complex vector spaces.
The imported `IsUnitary A` means that there exists an
`InnerProductSpace.Core ℂ A` preserved by every action operator. This core
includes positive definiteness and Hermitian sesquilinearity. Thus “unitary”
here means unitarizable. A particular form is neither part of the input nor
chosen by this statement.

## Declaration and dependency map

All declarations below are in `Langlands.FiniteRepresentation`.

| Proposition | Exact assertion | Imported mathematical definitions |
| --- | --- | --- |
| `UnitaryIsomorphismInvariance` | A genuine representation equivalence between `A` and `B` implies `IsUnitary A ↔ IsUnitary B`. | `Equiv` from `Langlands.Weil.Representation.Basic`, and `IsUnitary` from `Langlands.Weil.Representation.Predicates`. |
| `UnitaryDuality` | `IsUnitary (dual A) ↔ IsUnitary A`. | The same predicate and `dual` from `Langlands.Weil.Representation.Dual`. |
| `UnitaryTwisting` | If `‖(χ g : ℂ)‖ = 1` for every `g`, then `IsUnitary (twist χ A) ↔ IsUnitary A`. | The same predicate and `twist` from `Langlands.Weil.Representation.Twist`. |
| `UnitaryOperations` | The conjunction of all three propositions. | The preceding three targets in this module. |

`dual` is the full algebraic dual with action
`(r.dual g ℓ)(v) = ℓ(r(g⁻¹)v)`. It is not a selected smooth or topological
dual. `twist` retains the carrier and acts by `χ(g) r(g)`. Both are the
published constructors, which themselves reuse the existing generic dual and
character-twist interfaces. No duplicate representation or class construction
is introduced. The published `Langlands.Weil.Representation.Operations` target
is unchanged and is not assumed true by this module.

The group universe `uG` and carrier universes `uV`, `uU` are independent.
The equivalence clause compares different carrier universes. For complex
coefficients the dual carrier universe `max 0 uV` reduces to `uV`. Rank zero
is included. No irreducibility, semisimplicity, finite image, continuity,
inertia or topological-group premise is necessary for these algebraic
unitarizability statements. The modulus-one hypothesis is explicit; an
arbitrary unit-valued quasicharacter need not preserve unitarizability.

These results provide the unitary part of the later justification for dual and
twist maps on actual representation classes and lattice bases. This module
does not posit a class permutation, construct those restricted maps, or assert
their continuity or irreducibility properties. Those obligations use the
corresponding separate targets and constructors.

## Source correspondence and derived content

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), section 1.1, footnote 1, printed page 439 / PDF page 1,
distinguishes a continuous complex quasicharacter from a unitary character.
Section 1.2(2)–(3), printed page 440 / PDF page 2, fixes scalar tensor twists
and contragredients among the correspondence operations.

- Literature ID: `henniart-2000-simple-proof`.
- Original PDF SHA-256:
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Worker 25 read both original pages for this contribution and verified the
  original file hash.

That passage motivates the operation conventions and the unitary character
condition. It is not being cited as an explicit statement of these three
generic closure results. All three propositions are derived elementary
finite-dimensional Hermitian linear algebra with no local-field restriction.
For the equivalence clause, an invariant positive form transports along the
actual linear equivalence. For duality, the finite-dimensional dual Hermitian
form is invariant under the inverse-element dual action; applying this again
and the canonical bidual equivalence gives the converse. For a modulus-one
twist, the factor in the sesquilinear form is
`conj (χ(g)) * χ(g) = 1`, so the same form is invariant in either direction.
These explanations justify the target's scope, not a claim of implemented
Lean proofs.

The direct dependency pairs `Predicates`, `Dual` and `Twist` are published in
Library commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`. Their Lean
declarations, rather than submission identities, are the mathematical imports.
The pinned Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`; its `InnerProductSpace.Core`
supplies the positive-form laws used by `IsUnitary`.
