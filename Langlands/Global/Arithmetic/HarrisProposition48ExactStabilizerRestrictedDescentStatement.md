# The singleton branch and the reduction of Proposition 4.8 under the exact-stabilizer condition, with restricted supercuspidal descent

The module
`Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerRestrictedDescentStatement`
defines four unproved propositions in the namespace `Langlands.Global.Harris`.
All have universe parameters `uF uV`:

- `Proposition48ExactStabilizerRestrictedSingletonBranchStatement`;
- `Proposition48ExactStabilizerRestrictedSingletonBranchTCStatement`;
- `Proposition48ExactStabilizerRestrictedReductionStatement`;
- `Proposition48ExactStabilizerRestrictedReductionTCStatement`.

They are the published singleton branch, the published reduction and their
totally complex (TC) forms for Harris (1998), Proposition 4.8, under condition
(4.12), the exact-stabilizer condition. Modules:
`HarrisProposition48ExactStabilizerBranchStatement` and
`HarrisProposition48ExactStabilizerReductionStatement`. There is one change:
the restricted supercuspidal descent B5r
(`RestrictedCyclicWeakBaseChangeSupercuspidalStatement`, module
`Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeSupercuspidalStatement`)
replaces B5 (`CyclicWeakBaseChangeSupercuspidalStatement`). The TC forms use
the TC form of B5r in place of the TC form of B5. Everything else is unchanged:
every other premise, the premise order, the universe instantiations and the
bodies. The module proves nothing.

With this change the singleton branch and its TC form use B5r, with `v'` the
conjugate place. Canonical B5 stays published, but the branches do not use
it. The published statements with B5 stay in the Library unchanged.

## 1. The restricted singleton branch

`Proposition48ExactStabilizerRestrictedSingletonBranchStatement.{uF, uV}` is
`Proposition48ExactStabilizerSingletonBranchStatement.{uF, uV}` with its fifth
premise replaced. The full premise order is:

1. `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}`;
2. `CuspidalSpectralRigidityStatement.{0, uV}`;
3. `Proposition48IsobaricInvarianceStatement.{uV}`;
4. `CyclicStableDescentStatement.{0, 0, uV, uV}`;
5. `RestrictedCyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}`
   (B5r; the published branch has B5 here);
6. `RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV}`;
7. `CuspidalComplexParameterBridgeTCStatement.{0}`.

The body is the published one. For every problem `Q` and step `D` with
`Q.IsAuxiliaryExactStabilizerValid`, `Q.IsPrimeCyclicStep D` and one Mackey
class, if each child has an untwisted solution with the child's induced
complex-place parameters (the published hypothesis, unchanged), then
`Q.HasParameterSolution`.

`Proposition48ExactStabilizerRestrictedSingletonBranchTCStatement.{uF, uV}` is
`Proposition48ExactStabilizerSingletonBranchTCStatement.{uF, uV}` with
`RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV}` in
place of `CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV}`. The
other TC premises are those of the published TC branch:
`CuspidalSpectralRigidityTCStatement`, `Proposition48IsobaricInvarianceTCStatement`
and `CyclicStableDescentTCStatement`. Theorem 1.2, restricted B7 and the
bridge are as in the ordinary form. The body is unchanged.

### Where the branch applies B5r, and why it has the hypothesis there

The branch applies B5r once. The descent `S` over `E = Q.E` of the child's
constituent `T` over `D` must be supercuspidal at the auxiliary place
`v = Q.Ps.v`. The descent comes from B1, chosen to weakly induce `ξ`. B5r is
applied to the step `D/E` with `v = Q.Ps.v` and `v' = conjPlace Q.E Q.Ps.v`.
Its hypotheses then hold, and their proofs are obligations of the branch proof
(Section 3):

- `D/E` is Galois of prime degree, from `Q.IsPrimeCyclicStep D`.
- `v' ≠ v`. The auxiliary place lies over a place split in the imaginary
  quadratic field `K₀`, so it differs from its conjugate. The published
  branch proofs already need this for restricted B7.
- The unique places `w` above `v` and `w'` above `v'` in `D` come from
  `HasUniquePlaceAbove Q.L` at `Q.Ps.v` and at its conjugate, in the validity
  data, since `D ⊆ Q.L`.
- `T` is supercuspidal at `w` and at `w'`. The child's solution is
  supercuspidal above the child's auxiliary place, and it is conjugate
  self-dual, so it is also supercuspidal above the conjugate place. This is the
  same lemma the published branch proofs need for restricted B7. By
  `cuspidalAllLocalIrreduciblePresentationExistence` and
  `CuspidalSpectralPresentation.localComponent_isoClass_eq`, one presentation
  of `T` has both supercuspidal components, as B5r's single presentation
  binder requires.
- `[IsUnramifiedAtInfinitePlaces Q.E D]` (general form only): `Q.E` is CM,
  hence totally complex, so every infinite place of `D` is unramified over
  `Q.E` (Mathlib `NumberField.InfinitePlace.isUnramified_iff`). The TC form of
  B5r has no such instance.
- The unitarity of the central character of `S`, and the weak base change from
  `S` to `T`, are as in the published singleton branch with B5.

## 2. The restricted reduction

`Proposition48ExactStabilizerRestrictedReductionStatement.{uF, uV}` is
`Proposition48ExactStabilizerReductionStatement.{uF, uV}` with two of its
twenty-two conjuncts replaced, at the same positions:

| Position | Published conjunct | Restricted conjunct |
| --- | --- | --- |
| 10 | `Proposition48ExactStabilizerSingletonBranchStatement.{uF, uV}` | `Proposition48ExactStabilizerRestrictedSingletonBranchStatement.{uF, uV}` |
| 18 | `CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}` | `RestrictedCyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}` |

The other twenty conjuncts are unchanged, and so is the conclusion
`Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}`. These are the rank
one, normalization, untwist, Mackey and inheritance statements, distinctness,
the prime branch, Theorem 1.2, C2, invariance, B1–B4, B6, III.4.2(c),
restricted B7 and the bridge.

`Proposition48ExactStabilizerRestrictedReductionTCStatement.{uF, uV}` is
`Proposition48ExactStabilizerReductionTCStatement.{uF, uV}` with the same two
replacements in TC form: position 10 is the restricted singleton branch TC
form, and position 18 is
`RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV}`. The
conclusion is the same.

Canonical B5 is no longer a conjunct of the restricted reductions. Canonical
B6 (`TowerBaseChangeHeckeComponentStatement`) remains a conjunct, because the
distinctness statement uses it, as in the published reduction. That use is the
isolated distinctness lemma, `Proposition48ExactStabilizerDistinctnessStatement`.

## 3. Relation to the published statements, and proof obligations

- **The restricted forms imply the published ones.** B5 implies B5r, by
  dropping the second place and the extra hypothesis and forgetting the
  instance (see the Markdown of B5r). So the restricted singleton branch
  implies the published singleton branch: given B5, pass B5r to the
  restricted branch. The restricted reduction implies the published
  reduction: from the published conjuncts, conjunct 18 (B5) gives B5r, and the
  published singleton branch together with B5 gives the restricted singleton
  branch, without using the B5r premise. The same holds for the TC
  forms. A check outside the Library compiled all four implications. A proof of a restricted
  statement therefore also yields the published statement, as a corollary.
  The converses are not claimed.
- **Proof obligations of the restricted singleton branch.** These are those of
  the published singleton branch (its Markdown, "Why the branches should
  hold"), with B5r applied in place of B5 as in Section 1. The only new
  obligations are the B5r hypotheses at `w'` and the instance at the infinite
  places. The first coincides with what restricted B7 already needs. The
  second follows from Mathlib, as described above.
- **Proof obligations of the restricted reduction.** These are those of the
  published reduction (its Markdown): strong induction on the induction
  degree, normalization, untwisting, the inheritance statements, and the
  branches. With one Mackey class, the step applies input 10, now the
  restricted singleton branch, whose B5r premise is input 18.

## Sources

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, source `harris-1998-local-langlands`,
Proposition 4.8, printed p.201, and its proof, pp.201–203: the induction and
the singleton case. Condition (4.12): proof of Lemma 4.7, printed p.204.

Design: the plan note, source
`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
Section 2.2 (B5–B7, TeX lines 196–199) and Section 4.8 (Remark 4.2 and the
singleton branch, TeX lines 859–909). The classes of Harris's argument are
supercuspidal at two non-split conjugate places (TeX lines 202 and 758).
