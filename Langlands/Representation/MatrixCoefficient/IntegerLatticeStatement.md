# Exponential-polynomial matrix coefficients on the integer lattice

Authors: Worker 664, with Worker 6's representation-form formulation and prior
elaboration diagnostic as input.

`Langlands.IntegerLatticeMatrixCoefficientExponentialPolynomialStatement.{u}`
is a closed Prop-valued definition in
`Langlands.Representation.MatrixCoefficient.IntegerLatticeStatement`. It states
the matrix-coefficient proposition in Renard's Appendix C.III. A proof of the
proposition is a separate obligation.

## Original source and errata

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix C.III, printed pp.279–280, one-based PDF pages
285–286. The displayed proposition and its coefficient definition are on
p.279; the proof continues on p.280. Both pages were read, including their
rendered formulas.

- Literature ID: `renard-2026-representations-groupes-reductifs-padiques`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Retained original:
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

On 26 October 2026, the [author's book page](https://perso.pages.math.cnrs.fr/users/david.renard/)
linked the corrected 2026 French edition and a separate erratum explicitly
labeled for the 2010 edition. Its book section listed no separate 2026 errata.
The live French PDF and the linked erratum were downloaded for comparison;
their bytes matched the retained book above and the registered erratum below.
This is an observation about the author's linked materials on that date.

The registered author-page snapshot is `renard-author-page-2026-10-26`, retained
as `/home/taskhub/pilot/literature/David Renard — Author page and 2026-2010 book edition and errata links (snapshot 26 October 2026).html`.
The supplementary source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained as `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its appendix corrections on PDF18–19 were read. The final entry, for printed
p.322, line -4 of the old edition, inserts parentheses around the
scalar-times-unipotent factor before taking its integer power. The governing
2026 formula on p.280 already has those parentheses. The entry does not change
the displayed matrix-coefficient proposition. No project file
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` was
present at the inspected Library base. The 2010 erratum is supplementary;
the 2026 French edition governs this statement.

## Exact quantifiers and constructions

The proposition universally quantifies over each natural `d`, an arbitrary
carrier `V : Type u`, its additive commutative group and complex module
structures, and a `FiniteDimensional ℂ V` instance. These encode the source's
finite-dimensional complex vector space without choosing a basis or fixing its
carrier universe.

It then quantifies over a representation
`ρ : Representation ℂ (Multiplicative (Fin d → ℤ)) V`, every vector `v : V`,
and every functional `ell : Module.Dual ℂ V`. The source first presents
commuting invertible endomorphisms and then identifies their data with a
representation `U` of the additive group `ℤ^d`. This statement uses that
representation formulation directly. Mathlib's `Representation` is a monoid
homomorphism into linear endomorphisms. Its source here is a group, so the
action maps have inverses, supplied by the action of the inverse group
element; commutativity of the source makes these maps commute. No chosen
eigenbasis or decomposition is a premise.

`Fin d → ℤ` is the additive integer lattice, with coordinates indexed from
zero rather than the source's one-based indexing. `Multiplicative` changes
the notation of its group law, so that the existing multiplicative
representation and character APIs apply: `ofAdd (n + m)` is the product of
`ofAdd n` and `ofAdd m`. It does not change the lattice or remove negative
coordinates.

`Langlands.matrixCoefficient ρ ell v (Multiplicative.ofAdd n)` reduces to
`ell (ρ (Multiplicative.ofAdd n) v)`. This is exactly the source's
`F(n) = λ(U(n) · v)`. `Module.Dual` is the full algebraic complex dual. The
action is at `n`; the formula introduces neither inverse action nor complex
conjugation.

For each such coefficient, the statement asserts the existence of a natural
`l`, a family
`χ : Fin l → Multiplicative (Fin d → ℤ) →* ℂˣ`, and a family
`Q : Fin l → MvPolynomial (Fin d) ℂ`. These are the source's finite lists of
characters and complex polynomials. A character takes values in the units
`ℂˣ`, so its values are nonzero and it is multiplicative for addition of
integer tuples. The coercion `(χ j (Multiplicative.ofAdd n) : ℂ)` supplies the
complex scalar in the sum. Units here are all nonzero complex numbers;
unitarity is not asserted.

`MvPolynomial (Fin d) ℂ` is the ordinary polynomial ring in `d` commuting
variables. `MvPolynomial.eval (fun i => (n i : ℂ)) (Q j)` evaluates its
variables at the integer coordinates through their canonical complex casts.
The polynomial exponents remain natural, while the evaluation points range
over all integers. This is precisely the source's `Q_j(n)`.

The three existential witnesses precede `∀ n : Fin d → ℤ`. Thus one finite
family, chosen for the fixed representation, vector and functional, satisfies

```text
matrixCoefficient ρ ell v (Multiplicative.ofAdd n) =
  ∑ j, (χ j (Multiplicative.ofAdd n) : ℂ) *
    MvPolynomial.eval (fun i => (n i : ℂ)) (Q j)
```

on the whole lattice. There is no chamber or eventual-region condition.
The displayed source proposition requires neither distinct characters nor a
degree bound, and the Lean target adds neither condition.

All natural `d` are retained, including `d = 0`, when the lattice is trivial
and the polynomial ring has no variables. The carrier may be the zero vector
space, and the coefficient may be zero. The natural `l` may be zero, with an
empty sum. These conventions make the degenerate cases explicit without
adding positivity or nontriviality assumptions to the source formulation.
There is no topology, smoothness, irreducibility, simultaneous
diagonalizability, or pre-existing expansion hypothesis.

## Imports and retained proof obligations

`Langlands.Representation.MatrixCoefficient.Definitions` supplies the existing
algebraic coefficient. Mathlib's `RepresentationTheory.Basic`, imported there,
supplies representations. `Mathlib.Algebra.MvPolynomial.Eval` supplies the
polynomials and evaluation; `Mathlib.Basic.Complex.Basic` supplies complex
scalars; `Mathlib.LinearAlgebra.FiniteDimensional.Defs` supplies the
finite-dimensionality predicate. The prepared Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`.

The construction equating commuting invertible tuples with lattice
representations is separate work owned by the parent task. This statement
neither implements that equivalence nor supplies a tuple-form specialization.
It needs no unpublished bridge as an import.

The source proof groups the simultaneous generalized weights into common
triangular blocks. On each block, each generator is a nonzero scalar times
`Id + N`, with the nilpotent parts commuting. It then expands all integer
powers using the finite binomial formula; nilpotence truncates the expansion,
and the binomial coefficients are polynomials in the integer coordinates.
The coefficient is obtained by applying the fixed vector and functional.
Simultaneous generalized-weight decomposition, common triangular bases,
scalar-times-unipotent form, commutation and nilpotence of the nilpotent
parts, the finite expansion for negative as well as nonnegative powers, and
polynomiality of the binomial coefficients remain proof or construction
obligations. This module imports no checked correspondence for those steps
and proves none of them. A future proof may document a different route.

Worker 6's earlier private elaboration diagnostic
`2f5f8b61-f899-48ed-a329-653016e47c3c` motivated the formulation; it is not
acceptance or proof evidence. This contribution names and documents the
actual statement for independent review.
