# Zero-action separation of unitized finiteness conventions

Author: Worker 709. This is a statement-only internal derived unit for
whole-book Renard task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 2.

The module `Langlands.Algebra.UnitizationZeroActionFinitenessStatements`
uses the actual public `CompatibleUnitization.module` on the fixed carrier
ℂ with the zero action. `ComplexZeroActionStatement` says that for every
bilinear nonunital complex algebra A, its actual complex-unitized module
is both `Module.Finite (Unitization ℂ A) ℂ` and
`IsNoetherian (Unitization ℂ A) ℂ`. `IntegerZeroActionStatement` says that
for every nonunital ring A its actual integer-unitized module on ℂ is
neither finite nor Noetherian. `ZeroActionFinitenessStatements` is their
conjunction in that order. The algebra universe uA is arbitrary; the fixed
complex carrier has universe 0. Each target selects its actual module
locally with `letI`; there is no new action constructor or global instance.

The positive target quantifies over `A : Type uA` with `NonUnitalRing A`,
`Module ℂ A`, `IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`. These give
the full bilinear nonunital complex-algebra interface without requiring
commutativity. Its chosen action is
`0 : A →ₙₐ[ℂ] Module.End ℂ ℂ`. The negative target only requires
`NonUnitalRing A`, with action `0 : A →ₙₐ[ℤ] Module.End ℤ ℂ`.
Both use the existing `CompatibleUnitization.module`. The local module
argument of each finite/Noetherian predicate is precisely this chosen
module. The complex carrier and its additive group are fixed, and the
negative target uses its canonical integer scalar action.

These are internal derived comparisons, not assertions quoted from Renard
or a resolution of his finiteness convention. For the same complex algebra
A the original A-action in both branches is zero on the same carrier.
The adjoined scalar actions differ: `x` acts by `x.fst` times the vector,
over ℂ or ℤ respectively, by `CompatibleUnitization.zero_smul_eq`.
Thus finiteness and Noetherianity over the complex unitization do not
automatically imply the corresponding properties over the integer
unitization. All predicates here are ordinary module predicates over the
displayed unital rings. Neither ring Noetherianity nor a finite-generation
premise is assumed. Zero and nonzero algebras are allowed, and the actions
are degenerate.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The global conventions on printed page 6/PDF page 12 allow nonunital
rings and actions. The complex unit-adjoining construction and comparison
of complex-linear and algebra-linear Hom spaces in I.2.1, printed page
14/PDF page 20, motivate distinguishing the added scalars. The
finite-generation and Noetherian object definitions in A.I.3, PDF pages
254–255, and the final C.II proposition, printed page 279/PDF page 285,
motivate asking about these predicates. Those passages were read in full;
the I.2.1 page was also inspected visually. This module supplies a
concrete comparison of two explicit modern module conventions. It
does not identify either convention with the book's source definitions,
provide a counterexample to the book, or settle the source-facing C.II
proposition.

The registered older supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 18–19, was read as supplementary errata. It gives no resolution
of this convention question and does not supersede the 2026 original.
No project or current Library `notes/errata` directory was present at
the source audit.

A separate private feasibility check implements the following derivation.
For the positive branch, the complex line is finite and Noetherian over
ℂ, and the scalar tower given by
`CompatibleUnitization.isScalarTower` transfers both properties to its
actual complex unitization action. For the negative branch, the
semilinear identity along `(Unitization.fstHom ℤ A).toRingHom` is
surjective and respects the actual zero action. Finiteness over the
integer unitization would therefore imply finiteness over ℤ and hence
countability, contradicting the uncountability of ℂ. Noetherianity would
imply the same forbidden finiteness. This is a derivation rationale;
no theorem is proved in this statement module.

Development checks in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the canonical aggregate with zero errors or warnings and
`statement_returns_prop: true`; recovery diagnostic
`358f589b-7353-40f8-93f8-1967ebb95356` retains that result. Diagnostic
`05ae9e59-c6c7-4138-b18e-a9e886b70780` inspected all three complete
bodies and unapplied types, instantiated `uA` at 0 and 1, and checked
both complete telescopes with explicit module arguments by `Iff.rfl`.
The aggregate has universe parameter `uA` and only the standard
`propext`, `Classical.choice` and `Quot.sound` assumptions. The separate
private feasibility module also compiled cleanly, most recently in
`e0be3b25-8dad-4a16-9123-281e8d5f95a8`. These development checks supply
neither independent semantic acceptance nor an accepted proof.
