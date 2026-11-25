# The branches of Proposition 4.8 under the exact-stabilizer condition

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerBranchStatement`,
namespace `Langlands.Global.Harris`.

The module declares `universe uF uV` and sets `autoImplicit false`. Each of
the four declarations is a closed proposition definition with universes
`.{uF, uV}` and result `Prop`. `r : ℕ` means `GL_(r+1)`. The global number
fields in `Proposition48Problem.{uF}` are in `Type`; the leading zeros in
the global-input instantiations below are intentional.

Four unproved implications: the prime-orbit and singleton branches of the
induction for Harris 1998, Proposition 4.8, when the auxiliary character
satisfies condition (4.12) instead of general position, and their totally
complex (TC) forms. **None of them is proved here.** Each is its general-position
counterpart (`Proposition48PrimeBranchStatement`,
`Proposition48SingletonBranchStatement`, and the TC forms in
`HarrisProposition48ReductionTCStatement`) with exactly the changes listed
below. All other premises, binders, conjuncts and universes are as in those
counterparts.

## Common changes to all four

- `Q.IsAuxiliaryValid` becomes `Q.IsAuxiliaryExactStabilizerValid`.
- In the children, `R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1)`
  becomes `R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1)`.
- Each child gains the conjunct `R.HasInducedComplexPlaceParameters S.isoClass`
  after `R.IsUntwistedSolution.{uF, uV} ν S T`: the untwisted constituent `S`
  has, at every complex place of `R.E`, the parameters of the representation
  induced from `R.ξ`.
- The conclusion `Q.HasSolution.{uF, uV}` becomes
  `Q.HasParameterSolution.{uF, uV}`, which adds the induced complex-place
  parameters of `Q` to the four properties of `Q.HasSolution`.
- Two premises are added at the end of the named global inputs:
  `RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV}`
  (restricted B7, for complex-place parameters across a prime cyclic step with
  supercuspidal components at a conjugate pair of places) and
  `CuspidalComplexParameterBridgeTCStatement.{0}` (the archimedean bridge).
  Both are stated for CM, respectively totally complex, base fields; `Q.E` is
  a CM field, and the fields of the steps are totally complex. Neither has a
  separate TC form, so the TC branches take the same two premises.

The common quantified child hypothesis is exactly

```lean
(∀ a : Q.L ≃ₐ[Q.E] Q.L,
  ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
    (χs : FieldCharacter R.F R.F') (r : ℕ)
    (S T : CuspidalOperatorRealization R.E r),
    Q.IsAuxiliaryMackeyChild D a R ∧
    R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
    Module.finrank R.E R.E' = Q.mackeyRank D a ∧
    R.inductionDegree < Q.inductionDegree ∧
    R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
    R.IsUntwistedSolution.{uF, uV} ν S T ∧
    R.HasInducedComplexPlaceParameters S.isoClass)
```

After their named premises, all four declarations quantify
`∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)`.
The prime forms then have, in order, `Q.IsAuxiliaryExactStabilizerValid`,
`Q.IsPrimeCyclicStep D`,
`Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D`,
`Q.HasDistinctMackeyComponents.{uF, uV} D`, and the child hypothesis above,
as implication premises, concluding `Q.HasParameterSolution.{uF, uV}`.
The singleton forms omit the distinctness hypothesis and replace the
cardinality condition by `Nat.card (Q.MackeyIndex D) = 1`; every other binder
and conjunct of this body is identical.

## Prime branch: `Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV}`

Further changes:

- The premise `HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV}`
  (Harris's comparison at a split supercuspidal place, A2) is removed.
- The hypothesis `Q.HasDistinctMackeyComponents.{uF, uV} D` is added after the
  cardinality condition `Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D`.

The full named-premise order and universes are:

1. `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}`;
2. `CuspidalSpectralRigidityStatement.{0, uV}`;
3. `Proposition48IsobaricInvarianceStatement.{uV}`;
4. `CyclicRegularInductionStatement.{0, 0, uV, uV}`;
5. `CyclicRegularOrbitLiftStatement.{0, 0, uV, uV}`;
6. `CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}`;
7. `RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV}`;
8. `CuspidalComplexParameterBridgeTCStatement.{0}`.

In the general-position branch, A2 and general position serve to show that the
Mackey constituents of different double cosets have different supercuspidal
components above the auxiliary place. Under (4.12) this distinctness is the
separate statement `Proposition48ExactStabilizerDistinctnessStatement`, which
derives it from B6; the reduction supplies it. Because the children's
solutions carry their complex-place parameters, regular algebraicity of the
induced class is read off its parameters, and no premise about archimedean
components along base-change chains is needed.

## Singleton branch: `Proposition48ExactStabilizerSingletonBranchStatement.{uF, uV}`

Further change: the premise
`CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}` (B5) is added after
`CyclicStableDescentStatement.{0, 0, uV, uV}`. None of the general-position premises
says anything at the auxiliary place, and the conclusion does: the selected
descent must be supercuspidal at `Q.Ps.v`. B5 gives this from the
supercuspidal component of its base change, the child's constituent. This is
claim (3) of Remark 4.2 of the plan note for a fibre with one element (plan
line 909).

The full named-premise order and universes are:

1. `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}`;
2. `CuspidalSpectralRigidityStatement.{0, uV}`;
3. `Proposition48IsobaricInvarianceStatement.{uV}`;
4. `CyclicStableDescentStatement.{0, 0, uV, uV}`;
5. `CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}`;
6. `RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV}`;
7. `CuspidalComplexParameterBridgeTCStatement.{0}`.

## TC forms

`Proposition48ExactStabilizerPrimeBranchTCStatement` and
`Proposition48ExactStabilizerSingletonBranchTCStatement` are the two branches
above with exactly the following premise replacements, preserving their
positions and universe instantiations:

| Ordinary premise | TC premise |
| --- | --- |
| `CuspidalSpectralRigidityStatement.{0, uV}` | `CuspidalSpectralRigidityTCStatement.{0, uV}` |
| `Proposition48IsobaricInvarianceStatement.{uV}` | `Proposition48IsobaricInvarianceTCStatement.{uV}` |
| `CyclicRegularInductionStatement.{0, 0, uV, uV}` (prime) | `CyclicRegularInductionTCStatement.{0, 0, uV, uV}` |
| `CyclicRegularOrbitLiftStatement.{0, 0, uV, uV}` (prime) | `CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV}` |
| `CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}` (prime) | `CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV}` |
| `CyclicStableDescentStatement.{0, 0, uV, uV}` (singleton) | `CyclicStableDescentTCStatement.{0, 0, uV, uV}` |
| `CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}` (singleton) | `CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV}` |

Compared directly with `Proposition48PrimeBranchTCStatement`
and `Proposition48SingletonBranchTCStatement` in
`HarrisProposition48ReductionTCStatement`, the common changes and the
respective prime or singleton changes listed above are the complete changes.
Every other premise, binder and universe is unchanged. Theorem 1.2,
restricted B7, the bridge and the body are identical to the ordinary
exact-stabilizer forms.

## Why the branches should hold (proof obligations)

This is a sketch of a proof, not a proof.

*Prime branch.* For each `a`, the child supplies an untwisted constituent
`S_a` over `R.E ≅ D`: a weak induction of the Mackey character, conjugate
self-dual, supercuspidal at the child's auxiliary place, with the parameters
induced from the Mackey character. As in the general-position branch, transport
`S_a` to `D` and use rigidity and isobaric invariance to identify its
Galois translates with the classes indexed by the translates of its Mackey
class. The transitive action on the `[D : E]` Mackey classes has trivial
stabilizers. `HasDistinctMackeyComponents` distinguishes the corresponding
constituents, giving the trivial stabilizer required by restricted B7(2).
Arthur–Clozel induction (B2, B3)
gives a cuspidal class `Π` over `E` inducing one constituent, B4 gives its
supercuspidal component at `Q.Ps.v`, and Mackey's formula gives weak induction
of `ξ`; conjugate self-duality is as in the general-position branch. Restricted B7(2)
applied to `S_a` and `Π` gives the parameters of `Π` at a complex place `v` as
the Langlands sum of those of `S_a` at the places of `D` above `v`; Mackey's
formula for the induced parameters (a `List.Perm` identity) turns this into
`Q.HasInducedComplexPlaceParameters`. Regular algebraicity of `Π` follows from
the bridge, because the induced parameters satisfy Clozel's integrality and
regularity (`IsAlgebraicAfterTwist` and `IsRelativelyRegular` of `ξ`).

The proof must establish, not assume: unitarity of the central characters of
`S_a` and `Π`; supercuspidality at the conjugate place `conjPlace Q.E Q.Ps.v`
(from conjugate self-duality); `Q.Ps.v ≠ conjPlace Q.E Q.Ps.v` (from the split
imaginary quadratic field `K₀`); the unique places of `D` above these two
places (from `HasUniquePlaceAbove Q.L`); the transport of `S_a` and its
parameters from `R.E` to `D`; and the permutation identities.

*Singleton branch.* There is one Mackey class, so the child's constituent `S`
over `D` is Galois stable by invariance, and B1 gives its cyclic descents to
`E`. The general-position branch selects the descent that weakly induces `ξ`. B5
gives its supercuspidal component at `Q.Ps.v`. Restricted B7(1) relates the
parameters of the descent at `v` to those of `S` at a place `w` of `D` above
`v`. The singleton parameter identity must identify the list at `w` with
the transport of `Q`'s induced list at `v`, up to permutation. This gives
the descent the induced parameters of `Q`. Regular algebraicity follows
from the bridge as in the prime branch.

## Sources

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, source `harris-1998-local-langlands`,
Proposition 4.8, printed p.201, and its proof, pp.201–203: the induction,
prime-orbit case and singleton case. Condition (4.12): proof of Lemma 4.7,
printed p.204.

Design: the operator's plan note, source
`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
Section 2.2 (B5–B7, TeX lines 196–199) and Section 4.8 (Remark 4.2, lines
859–894; the prime branch, line 908; the singleton branch, line 909; B7,
line 911). The restriction of B7 to supercuspidal components at a conjugate
pair and the parameter-carrying solutions are a later design decision
for these branches (option R2), which replaces the use of canonical B7 on the
members of base-change chains.

Restricted B7 has no
algebraicity hypothesis on either class: its later applications must establish
unitarity and supercuspidality at the auxiliary conjugate pair, then use the
children's parameters and the bridge for regular algebraicity. In particular,
restricted B7(2) supplies the prime output's parameters and restricted B7(1)
supplies the singleton output's parameters. Canonical B7(3), whole-tower
archimedean transport and an endpoint lemma beyond rank one are not premises.

The parameter predicates, distinctness and these parameter-carrying branches
are internal interfaces of R2, not statements of Harris. These are unproved
restatements of the general-position branch interfaces; all proof obligations in
the sketches remain obligations. No existing declaration is changed.
