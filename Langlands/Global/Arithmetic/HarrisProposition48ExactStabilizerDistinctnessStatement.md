# Distinct Mackey components under the exact-stabilizer condition

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessStatement`,
namespace `Langlands.Global.Harris`.

The module declares `universe uF uV`, sets `autoImplicit false`, and defines
two closed propositions with universes `.{uF, uV}` and result `Prop`.
`r : ℕ` in the expanded distinctness predicate means `GL_(r+1)`.

Two implications. **Neither is proved here.** They are proved as
`proposition48ExactStabilizerDistinctness` in
`HarrisProposition48ExactStabilizerDistinctnessProof` and
`proposition48ExactStabilizerDistinctnessTC` in
`HarrisProposition48ExactStabilizerDistinctnessTCProof`.

## `Proposition48ExactStabilizerDistinctnessStatement.{uF, uV}`

```lean
TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV} →
CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV} →
CuspidalSpectralRigidityStatement.{0, uV} →
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
    Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
    Q.HasDistinctMackeyComponents.{uF, uV} D
```

The premises are B6 (the tower comparison of Hecke components, with supplied
unitary isobaric chains), Arthur–Clozel III.4.2(c) for prime cyclic base
change of unitary isobaric data (`CyclicPrimeIsobaricBaseChangeStatement`,
Library module `Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement`),
and rigidity. The hypotheses on `Q` and
`D` are those of the prime branch: exact-stabilizer validity, a Galois cyclic
step of prime degree, and `[D : E]` Mackey classes. The conclusion is
`HasDistinctMackeyComponents` of the sibling module
`HarrisProposition48ExactStabilizerParameterData`: Mackey constituents over
`D` with unitary central characters for different double cosets have
non-isomorphic components at every place of `D` above `Q.Ps.v`.

## `Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV}`

The same statement with the three premises replaced by
`TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV}`,
`CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV}` and
`CuspidalSpectralRigidityTCStatement.{0, uV}`. The fields to which they are
applied, `D` and the fields of the tower above it, are extensions of the CM
field `Q.E`, hence totally complex. Every other premise, binder and universe,
including `Q : Proposition48Problem.{uF}`, the intermediate field `D`, the
cardinality condition and `Q.HasDistinctMackeyComponents.{uF, uV} D`, is
identical to the first declaration.

There is no general-position counterpart of either distinctness declaration. They
isolate the part of the general-position prime branch that uses A2
(`HarrisSupercuspidalLocalComparisonStatement`) and general position to
distinguish the local Mackey constituents. The exact-stabilizer prime branch
takes only this conclusion as a hypothesis; its derivation from B6, rather
than A2, is the separate implication here.

## Why it should hold (proof obligations)

This is claim (2) of Remark 4.2 of the plan note in the form of B6 (plan
Section 4.8, line 908). A sketch of a proof, not a proof:

1. `L` has exactly one place above `Q.Ps.v` (`HasUniquePlaceAbove`, a
   conjunct of validity), so so has `D`, and the places `w` in the conclusion
   are this one place. `Gal(L/E)` is then the decomposition group of the
   place of `L`, a Galois group of finite extensions of `p`-adic fields, hence
   solvable. So `L/D` is the top of a tower of prime cyclic steps starting at
   `D` (`PrimeCyclicBaseChangeTower`).
2. For a Mackey constituent `T` for `a`, III.4.2(c), applied step by step,
   gives a unitary isobaric chain of successive weak base changes starting at
   `T`. Over `L`, the base change of the induction of `a(ξ) ∘ N` is the sum of
   the Galois conjugates of `a(ξ) ∘ N_{L/a(E')}`, a family of Hecke
   characters (unitary after the normalization the premises require);
   rigidity identifies the end of the chain with this family.
3. For `a`, `a'` in different double cosets the two families do not have the
   same components at the place of `L` above `Q.Ps.v`. This is where (4.12)
   is used (`HasExactWeilStabilizer`): the stabilizer in `W_F` of the
   restriction `χ̃` of the Weil character of `χs` to the Weil group of `F̃`
   is exactly `W_{F'}`. So the conjugates of `χ̃` are pairwise distinct. The
   components of the two families are the conjugates indexed by the two
   fibres of the double cosets, and these fibres are disjoint (plan, Remark
   4.2, proof of claim (2)).
4. B6 then gives that the components of `T` and `U` above `Q.Ps.v` differ.

The proof must also supply the unitary normalizations the premises require
(unitary isobaric data, unitary Hecke characters) and the transport between
`D`, the tower levels and `L`.

## Sources

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, source `harris-1998-local-langlands`,
Proposition 4.8, printed p.201, and its proof, pp.201–203 (especially the
prime-orbit case); condition (4.12) in the proof of Lemma 4.7, printed p.204.

Design: the operator's plan note, source
`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
Section 2.2 (B5–B7, TeX lines 196–199) and Section 4.8 (Remark 4.2, lines
859–894; the branch paragraphs, lines 908–912; the decision for B6 as stated in
Section 2.2, lines 920–921). J. Arthur and L. Clozel, *Simple algebras, base
change, and the advanced theory of the trace formula*, Ann. of Math. Stud.
120 (1989), source `arthur-clozel-1989-base-change`, Chapter III,
Theorem 4.2(c) (weak lifting for cyclic extensions of prime degree, for
representations induced from cuspidal), printed p.202 (PDF p.216).

The design decision R2 retains standard B6 (B6 as stated in the plan note,
Section 2.2) through this isolated conclusion.
It uses parameters carried by solutions with restricted B7(2) in the prime
branch and B7(1) in the singleton branch, followed by the separate
archimedean bridge. No whole-tower archimedean transport is needed by the
branches.

The distinctness predicate and these implications are internal interfaces of
R2, not statements of Harris or Arthur–Clozel. The parameter predicates and
parameter statements used by the sibling branch modules are internal as
well.

## Status

Proposition definitions only. Neither implication is proved here, and no
existing declaration is changed.
