# Internal Noetherian unitization criteria

This statement-only module specifies three derived algebraic targets and their
conjunction. It contains no proofs of these targets. The scalar ring and the
possibly noncommutative nonunital ring have independent universes `uR` and `uA`.

For a commutative unital ring `R` and a nonunital ring `A`, the structures
`Module R A`, `IsScalarTower R A A` and `SMulCommClass R A A` express scalar
linearity of multiplication in both arguments. Let `U = Unitization R A`,
Mathlib's actual unitization, and let
`I = RingHom.ker (Unitization.fstHom R A)`. This is the actual kernel ideal of
the scalar-coordinate homomorphism, with its inherited ordinary left
`U`-module structure.

- `KernelCriterionStatement` states
  `IsNoetherianRing U ↔ IsNoetherianRing R ∧ IsNoetherian U I`.
- `NoetherianScalarCriterionStatement` assumes `IsNoetherianRing R` and states
  `IsNoetherianRing U ↔ IsNoetherian U I`.
- `FieldCriterionStatement` specializes the latter equivalence to any field
  `k`, with no hypothesis of algebraic closure or characteristic zero.
- `UnitizationNoetherianStatement` is the conjunction of these three complete
  propositions, in that order.

Each target binds all its carriers and structures internally. In Mathlib,
`IsNoetherianRing U` means Noetherianity of the regular left `U`-module. No
commutativity or multiplicative unit of `A`, finite dimension, countability,
nontriviality of `A`, or Noetherianity assumption on `A` is imposed. The general
criterion does not assume that `R` is Noetherian; it includes that property on
the right side of the equivalence.

These are internal algebraic prerequisites motivated by Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, I.2.1 (printed page 14 / PDF page 20) and the final proposition of
C.II (printed page 279 / PDF page 285). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
They are derived targets, rather than claims that these formulas occur in the
book. Their algebraic rationale is the actual scalar-coordinate exact sequence:
its kernel is `I`, its middle term is `U`, and its quotient is `R`.

The module does not define Noetherianity or finite generation under the book's
possibly nonunital algebra and module conventions. Comparing the kernel ideal
with the actual unitized regular action on `A`, comparing compatible stable
scalar-linear subspaces, and transferring finite generation and Noetherianity
for the source's modules remain separate obligations over independently
published constructions. In particular, these statements alone do not show
that the hypotheses of the final C.II proposition imply Noetherianity of the
unitization or of its modules, and do not establish the actual localization
theorem.
