# Isotypic local trace factorization on an irreducible cuspidal summand (proof)

Module `Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationProof` contains one
theorem:

- `Langlands.TraceFormula.groupSchemeCuspidalIsotypicTraceFactorization :
  GroupSchemeCuspidalIsotypicTraceFactorizationStatement.{u}`, with the universe `u` left free.

The statement is in the module of the same name
([statement page](GroupSchemeCuspidalIsotypicTraceFactorizationStatement.md)). Let `P` be a
nonzero complete subspace of the group-scheme cuspidal space `S`. Assume `P` is invariant under
the right action `πc` of `G(𝔸_F)` and has no closed invariant subspaces other than `⊥` and `P`.
Let `v` be a finite place. The statement then gives an irreducible admissible representation `ρ`
of `G(F_v)` on a `Type u` carrier. This `ρ` occurs in `P` (clause 0), every smooth irreducible
representation occurring in `P` is isomorphic to it (clause 0'), and its character and twisted
character split off the traces on `P` (parts 1 and 2).

## The proof

The proof composes two theorems that are already in the Library.

1. **A local occurrence.** `Langlands.TraceFormula.groupSchemeCuspidalLocalOccurrence` (module
   `Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceProof`) proves
   `GroupSchemeCuspidalLocalOccurrenceStatement`. It has the same data and hypotheses on `P`
   as the target, including `P ≠ ⊥`, and gives the following: a carrier `V : Type u`, an
   irreducible admissible representation `ρ` of `G(F_v)` on `V`, and a nonzero linear map
   `j₀ : V → S` with range in `P` and `j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)`. Its
   proof first shows that the cuspidal convolution operators are compact. A spectral argument
   for an away-from-`v` convolution operator commuting with `G(F_v)` then gives a nonzero
   eigenspace whose compact-open fixed spaces are finite-dimensional. The irreducible admissible
   `ρ` is extracted from that eigenspace
   ([proof page](GroupSchemeCuspidalLocalOccurrenceProof.md)).
2. **From one occurrence to the full conclusion.**
   `Langlands.TraceFormula.IsotypicTrace.cuspidalIsotypicTraceFactorization_of_exists_occurrence`
   (module `Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction`) takes the target's
   data, `μv`, `ν`, `P` with its invariance and irreducibility hypotheses, and an occurrence
   exactly as in step 1. From these it proves the conclusion of
   `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` for `P`, with the same `ρ` and `j₀`.
   Clause 0 is the occurrence itself. The isotypy clause 0' and parts 1 and 2 come from a
   decomposition of `P` into a Hilbert sum of closures of occurrences of `ρ`, with the algebraic
   Schur lemma for admissible `ρ` on each summand
   ([reduction page](IsotypicTrace/CuspidalOccurrenceReduction.md)).

In Lean, the proof introduces the binders of the target statement, including the `let`-bound
`S` and `πc`, the summand `P` and its three hypotheses. It applies the theorem of step 2 to the
output of step 1. The only hypothesis used by step 1 but not by step 2 is `P ≠ ⊥`. Both theorems
are stated in the same universe `u` as the target, for the local carrier as well as the
carrier `V'` of clause 0'. They return `S`, `πc`, the integrated actions and the twisted
compressions in the same form as the target statement, so the two theorems compose with no
conversion. The theorem's axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Dependencies

- `Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement`: the statement
  proved.
- `Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceProof`:
  `groupSchemeCuspidalLocalOccurrence`.
- `Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction`:
  `cuspidalIsotypicTraceFactorization_of_exists_occurrence`.

## Correspondence with the sources

The statement page explains why the statement is true, by the following route. The Hilbert
tensor factorization `P ≅ π_v ⊗̂ π^v` holds because `G(F_v)` is of type I
(J. R. Getz and H. Hahn, *An introduction to automorphic representations*, 2024, registered
`getz-hahn-2024-automorphic-representations`, Theorem 3.10.2, printed p. 97; G. B. Folland,
*A course in abstract harmonic analysis*, 2nd ed., 2015, Theorem 7.17, printed p. 237). The
local factor `ρ` is taken on the smooth vectors of `π_v` (Getz–Hahn, Proposition 5.3.8 and
Theorem 5.3.9, printed p. 141). The isotypy clause is the analogue of the last sentence of the
proof of D. Flath, *Decomposition of representations into tensor products*, 1979, registered
`flath-1979-tensor-products`, Theorem 1, printed pp. 179–180.

The implemented proof takes a different route and does not use the type I property, a Hilbert
tensor product or the admissibility of irreducible unitary representations. Step 1 adapts the
nonzero eigenspace argument for compact cuspidal convolutions in Getz–Hahn §9.1–9.3 (Theorem
9.1.2, printed p. 241, and Lemma 9.3.1, printed p. 247), as its proof page describes. Step 2
uses a Hilbert sum of closures of occurrences of `ρ` in place of the tensor decomposition. It
uses the algebraic Schur lemma for the admissible irreducible `ρ` in place of Schur's lemma for
unitary representations (Folland, Theorem 3.5, printed p. 77). Flath's isotypy (Theorem 1) is
obtained in this form: each occurrence of a smooth irreducible `ρ'` in `P` projects nontrivially
to one of these closures and factors through the occurrence of `ρ` there.

The theorem gives in this generality the input that Henniart and Lemaire use in the global
step of cyclic base change. G. Henniart and B. Lemaire, *Changement de base et induction
automorphe pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.6.5, Proposition
(printed pp. 121–122), factor the global twisting operator on a cuspidal `Π ≅ ⊗'_v Π_v` as a
tensor product of local normalized operators. This makes the twisted trace in the comparison
of II.6.6 (printed p. 123) a product of local twisted traces. Part 2 gives this splitting at one
finite place `v`. The operator `Av` on the local factor plays the role of `A_{Π_v}`, and `C fw`
collects the contribution away from `v`.
