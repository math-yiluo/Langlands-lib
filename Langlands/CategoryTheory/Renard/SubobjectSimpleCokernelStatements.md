# Simple cokernels and covers of subobjects

`Langlands.Renard.SubobjectSimpleCokernelStatement C` is a derived internal
prerequisite for the Jordan–Hölder theorem in Renard 2026, Appendix A.VI.3.
It is a proposition definition, not a proof and not a separately numbered
assertion of the book.

## Exact assertion

```lean
def SubobjectSimpleCokernelStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (A B : Subobject X) (h : A ≤ B),
    Simple (cokernel (Subobject.ofLE A B h)) ↔ A ⋖ B
```

The object universe `u` and morphism universe `v` are independent. The only
assumptions are that `C` is a category and is abelian. Every object `X`, every
pair of actual subobjects `A, B` of `X`, and every inclusion inequality
`h : A ≤ B` are quantified.

`Subobject.ofLE A B h` is Mathlib's actual monomorphism between the underlying
objects of `A` and `B`, compatible with their arrows into `X`.
`cokernel` is the categorical cokernel of that monomorphism, representing
the quotient `B/A`. `Simple` is Mathlib's nonzero simplicity condition:
monomorphisms into the object are isomorphisms exactly when they are nonzero.
For an abelian category this agrees with the source's condition that the
object be nonzero and have only zero and full subobjects.

`A ⋖ B` is Mathlib's `CovBy` relation: `A < B` and there is no subobject
strictly between them. The equivalence includes both directions and every
inclusion, including `A = B`. In that case the quotient is a zero object and the cover
relation fails, so both sides are false. No positivity or nonzero premise
excludes that case.

There is no assumption of Grothendieck axioms, the source's later AB6
condition, well-poweredness, smallness, concreteness, module structure,
finite dimension, finite length, or a `JordanHolderLattice` instance.
The quotient is an actual object of `C`; it is not replaced by an
isomorphism class or an assumed factor.

## Provenance and purpose

The original passage is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.VI.2(9) and A.VI.3,
printed page 263 / PDF page 269. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source file is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Original PDF pages 268–269 were read directly, and PDF page 269 was also
visually inspected.

At A.VI.2(9) the source gives the Noether isomorphisms for actual subobjects
and quotients. At A.VI.3 it defines simple objects and composition series by
simple successive quotients, then states Jordan–Hölder and attributes its
proof to those isomorphisms. The criterion here is an internal bridge from
that categorical formulation to order covers on actual subobjects. The
book does not state it separately. Its additional Grothendieck and AB6
assumptions occur after Jordan–Hölder and are not added here.

The published `Langlands.CategoryTheory.Renard.CompositionChains` uses these
same actual subobjects, inclusions and cokernel factors. The published
`Langlands.CategoryTheory.Renard.JordanHolderStatements` states the equal
lengths and permutation of isomorphic factors. Those modules remain
unchanged. A later proof may use this criterion to translate composition
chains into Mathlib order-theoretic composition series and derive the
required lattice laws internally. Neither that translation nor
Jordan–Hölder is asserted proved by this module.

The public discrepancy note `notes/renard/appendix-a-corrections.md` records
no correction to A.VI.2(9) or A.VI.3. The registered supplementary 2010
corrections (`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`)
concern a different edition. Their appendix entries on PDF pages 18–19 were
read; they neither state this criterion nor correct the passage above.
This is a bounded observation, not a claim that no erratum exists elsewhere.

## Implementation and status

The module imports the public `Langlands.CategoryTheory.Renard.CompositionChains`
by Lean name and Mathlib's `Order.Cover`. The public import already supplies
Mathlib's `Simple`, `Subobject` and categorical cokernel constructions.
Its single new declaration is a `Prop`-valued `def`; it adds no proof,
instance, axiom, or replacement mathematical object. The separate proof
successor must prove this exact Library statement after publication.
Compilation and proposition inspection are development checks and do not
establish independent acceptance or publication.
