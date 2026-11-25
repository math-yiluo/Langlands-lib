# The prime-degree second inequality for actual idele classes

The theorem
`Langlands.Global.AdelicFunctoriality.ideleClassPrimeDegreeSecondInequality.{u,v}`
proves exactly the unchanged proposition
`Langlands.Global.AdelicFunctoriality.IdeleClassPrimeDegreeSecondInequality.{u,v}`.
For every Galois extension of number fields `L/K` of prime degree, it gives

\[
 [C_K:N_{L/K}(C_L)]\mid [L:K].
\]

The fields `K : Type u` and `L : Type v` have independent universes.
The norm is the published actual `ideleClassNorm`, and its range index is
`(ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index`.
There is no extra cyclicity, root-of-unity, cohomological, or finite-index
hypothesis. Every prime degree is included, including two. Since the
degree is positive, the divisibility also excludes the zero value of
`Subgroup.index` associated with an infinite quotient.

The proof composes published theorems. It first supplies the three inputs
of `ideleClassKummerPrimeDegreeSecondInequality_of.{v}`:

- `Langlands.Global.cyclicNonsplitPrimeStatement.{v,v}` supplies nonsplit
  finite primes outside any prescribed finite set;
- `Langlands.ClassFieldTheory.Global.ideleClassGaloisDescent.{v,v}` supplies
  descent for the actual idele classes;
- `Langlands.ClassFieldTheory.Global.cyclicIdeleClassHerbrandQuotient.{v,v}`
  supplies the cyclic Herbrand identity and both cohomology finiteness
  assertions.

This proves the root-containing Kummer case at universes `v,v`. The
imported Kummer proof derives cyclicity from
`IsGalois.card_aut_eq_finrank` and `isCyclic_of_prime_card`, then uses its
published auxiliary-prime, S-unit, local-power and norm-lifting arguments.
Its first-inequality input is discharged by the separate Herbrand proof.
That proof computes the quotient using ordinary units, integral ideles
and the finite residual idele-class quotient. Thus the first inequality
is a proved dependency rather than an assumption on the final theorem.

The assembly then applies
`ideleClassCyclotomicSecondInequalityReduction_holds.{u,v}`.
Its finite-index and degree-power antecedent is supplied by
`ideleClassNormIndexFinite.{u,v}`, and its norm tower antecedent by
`ideleClassNormTower.{u,v,v}`. The Kummer antecedent is the result just
obtained. The cyclotomic construction takes `M = L(ζ_p)` and
`E = K(ζ_p)` inside `M`, both with carriers in `Type v`. It proves that
`M/E` is Galois of degree `p` and that `[E:K]` is prime to `p`.
The two norm towers and the degree-power bounds then reduce the desired
divisibility to the Kummer conclusion for `M/E`. These carrier choices
explain why the same-universe Kummer theorem suffices for the independent
universes of the final target.

This module is an internal assembly of the existing Library interfaces;
it duplicates none of their constructions. The mathematical route is
Artin and Tate, *Class Field Theory* (2009), Chapter VI §1, Reduction 2
and the preceding index lemmas, printed pp.20–21 (PDF pp.29–30), followed
by the Kummer argument of VI §3, printed pp.24–27 (PDF pp.33–36).
The use of the first inequality on printed p.26 remains explicit in the
separate Herbrand dependency. The registered original is
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The imported modules' paired Markdown describes their implemented
arguments and their differences from the source.

The cyclotomic construction with its tower index lemmas, the Kummer proof,
the finite-index proof, the nonsplit-prime proof, the Herbrand assembly,
and the norm tower and Galois descent proofs are imported by name from
their published modules.
The target pair and all imported pairs are unchanged. The proof adds no
axiom and uses no global idele-class H¹ vanishing, general second
inequality, global reciprocity, or global fundamental class as an input.
