# Heterogeneous three-block associativity for normalized upper induction

Author: Worker 328.

`Langlands.Parabolic.ThreeBlockInductionAssociativityStatement` is a closed
Prop-valued definition. It states an actual representation equivalence between
`rho0 star (rho1 star rho2)` and `(rho0 star rho1) star rho2`, after an explicit
ambient rank transport. It does not prove associativity. Here `star` is only
explanatory notation for the literal construction specified below.

## Inputs and conclusion

For every prime `p` and `F : PadicField.{uF} p`, take positive natural ranks
`C`, `A`, `B` and complex representations `rho0`, `rho1`, `rho2` of
`GL_C(F)`, `GL_A(F)`, `GL_B(F)`. Their carriers `V0`, `V1`, `V2` live in
independent universes `uV0`, `uV1`, `uV2`. Each action satisfies `IsSmooth`
for the general linear group topology induced by
`F.canonicalTopologicalData.topology`. The four universe parameters are
independent; the proposition has no additional parameters outside its definition.

The conclusion is

```lean
Nonempty (Representation.Equiv (left.comp rankTransport.toMonoidHom) right)
```

where `left` and `right` are the two actual iterated induced actions. A witness
would be an invertible complex-linear intertwiner between their constructed
smooth-function carriers. The statement does not identify these carriers by
type equality and does not take an equivalence as an input.

## Literal induction and the four carrier lifts

Every induction node is exactly `F.canonicalNormalizedProductInduced` applied
to `Shahidi.twoBlocks` and `Shahidi.pairFamily`, in the displayed block order.
Thus each node uses the actual standard upper parabolic, right translation
on smooth covariant functions, and the canonical positive half modulus.
There is no spectral-parameter twist. This is the same pair construction as
`Langlands.RankinSelberg.InducedTailLFactorStatement`.

For a pair on carriers `V : Type u` and `W : Type v`, the statement uses
`ULift.{v} V` and `ULift.{u} W` and conjugates both actions by
`ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom`. The lifted action sends
`up(x)` to `up(rho(g)(x))`. Both block carriers then lie in `max u v`, and
the smooth induced carrier lies in `max uF u v`.

This rule is applied separately at all four nodes:

| Node | Ordered block ranks | Lift of first carrier | Lift of second carrier | Induced carrier universe |
| --- | --- | --- | --- | --- |
| `rho12` | `(A, B)` | `ULift.{uV2} V1` | `ULift.{uV1} V2` | `max uF uV1 uV2` |
| `left` | `(C, A + B)` | `ULift.{max uF uV1 uV2} V0` | `ULift.{uV0}` of the actual `rho12` carrier | `max uF uV0 uV1 uV2` |
| `rho01` | `(C, A)` | `ULift.{uV1} V0` | `ULift.{uV0} V1` | `max uF uV0 uV1` |
| `right` | `(C + A, B)` | `ULift.{uV2}` of the actual `rho01` carrier | `ULift.{max uF uV0 uV1} V2` | `max uF uV0 uV1 uV2` |

The Lean placeholders in the two inner-carrier type annotations are inferred
from the corresponding already constructed actions. All constructions are local
`let` expressions. No general regrouping definition or tensor adapter is added.
The existing `Category.UniverseLift` and `Induction.BlockEquivalence` modules
provide carrier transport infrastructure, but this statement keeps the exact
conjugation expressions required by its consumer.

## Direction and entries of the rank transport

Set `h := Nat.add_assoc C A B`, an equality
`(C + A) + B = C + (A + B)`. The local definition is

```lean
rankTransport : GeneralLinear ((C + A) + B) F.Carrier ≃*
    GeneralLinear (C + (A + B)) F.Carrier :=
  GeneralLinear.reindex (R := F.Carrier) (finCongr h)
```

For a matrix `g` of rank `(C + A) + B` and indices `i,j` of rank
`C + (A + B)`, its entry is
`rankTransport(g)(i,j) = g(Fin.cast h.symm i, Fin.cast h.symm j)`.
The casts retain the natural-number values of both indices. Hence coordinates
`0,...,C-1`, `C,...,C+A-1`, and `C+A,...,C+A+B-1` retain their positions,
and the ordered blocks remain `(C,A,B)`. There is no block permutation.

Precomposing `left` with this forward homomorphism yields the action
`g ↦ left(rankTransport(g))` on `GL_((C+A)+B)(F)`, the ambient group of
`right`. This is the direction in which a left action at rank `C+(A+B)`
is transported to the right rank. The map is fixed by the natural-number
equality and is not an arbitrary group equivalence supplied as a hypothesis.

## Original source and internal provenance

The motivation is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, section 9.3, printed pages 455–457, especially page 457.
The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The scan's one-based PDF pages 90–92 were read visually, and the fingerprint
was verified. Bounded checks of project and Library notes and the literature
index found no source-specific erratum affecting this passage.

On printed page 457, the proof for test rank at least the original induced
rank prepends quasicharacters. It expresses the enlarged representation both
by grouping those factors with the first original block and by grouping the
two original blocks first. Both displays use upper parabolics. This motivates
the present three-factor associativity adapter; the intended consumer can
specialize `C = 1` and repeat it for successive prepended characters.

The Lean proposition is an internal derived specialization of ordered
normalized induction in stages. JPSS does not print this exact proposition
for arbitrary smooth factors, its independent universes, its ULift carriers,
or its Fin rank casts. Those are explicit internal presentation choices.
The published `RefinementCoordinates` and
`RefinementInductionTransitivityProof` modules supply parts of the general
coordinate/refined-parabolic layer. They do not by themselves prove this
literal heterogeneous specialization. Its later proof must also supply the
appropriate tensor and carrier comparisons; none is assumed here.

## Scope and status

Smoothness of the original three actions is the only representation-theoretic
hypothesis. There is no Whittaker-type, irreducibility, admissibility,
finite-length, finite-dimensionality, or character assumption. The first rank
is arbitrary positive `C`; no rank-zero extension is made. The statement
assumes no modulus identity, tensor comparison, induction transitivity, or
conclusion-shaped input. It has no local-factor or analytic conclusion.

Development check `9f78fc87-6518-47d4-8683-e5abcd034462` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the declaration with zero
errors and warnings. Inspection reports `statement_returns_prop = true`,
level parameters `uF`, `uV0`, `uV1`, `uV2`, and only `propext`,
`Classical.choice`, and `Quot.sound`. This is statement validation, not a
proof of associativity or independent semantic acceptance.
