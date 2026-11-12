# Finite-type factorization through a smooth algebra

`Langlands.CommutativeAlgebra.PopescuFactorizationStatement.{u}` asserts
the following consequence of Popescu's theorem. Let `R` and `S` be
commutative Noetherian rings in `Type u`, with a specified `R`-algebra
structure on `S`. If `RegularAlgebra R S` holds, then every `R`-algebra map
`f : C →ₐ[R] S` from a finite-type commutative `R`-algebra `C : Type u`
factors exactly through a smooth `R`-algebra `B : Type u`.

The conclusion supplies the commutative ring and algebra structures on
`B`, the property `Algebra.Smooth R B`, and actual algebra maps
`g : C →ₐ[R] B` and `h : B →ₐ[R] S` with `h.comp g = f`.
Mathlib's smoothness property includes finite presentation.
The equation is equality of algebra maps into `S`, with no quotient or
approximation order.

The imported `RegularAlgebra` predicate means flatness of the specified
map `R → S` and geometric regularity of every actual prime fibre.
Noetherianity of both entire rings is an additional explicit hypothesis
here, as in the source theorem. There is no assumption that either ring
is a domain, reduced, local, or a finite-type integer algebra.
There is no smoothness assumption on `C`.
All quantified rings and the smooth witness stay in the single arbitrary
universe `u`.

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, version ed88ff78,
`smoothing.pdf`, Chapter 16, Section 16.12, Theorem 16.12.1
(Tag 07GC; printed as Theorem 12.1 on page 31).
It states that every regular map of Noetherian rings is a filtered
colimit of smooth ring maps. Since `R` is Noetherian, a finite-type
`R`-algebra `C` is finitely presented. The finite-presentation mapping
property then factors `f` through one smooth algebra in that filtered
system. This explains the exact factorization interface used here.
Finite-presentation smooth algebras over `R` admit presentations, and
hence representatives, in the universe of `R`.

This is a derived consequence of the cited theorem, rather than a
transcription of its filtered-colimit formulation. The module states
the proposition and contains no proof of Popescu's theorem, of the
filtered-colimit mapping property, or of this consequence. In particular,
it proves neither arithmetic completion regularity nor the unchanged
`FiniteTypeIntEtaleCompletionApproximationStatement`.
