# Exact Grothendieck classes of naturally glued smooth functors

Author: Worker 320.

This module defines the proposition
`Langlands.SmoothRep.FiltrationGrothendieckStatement.{uR,uG,uV,uC,vC} R G`.
It supplies a target for passing from an actual natural finite filtration
to an equality in the exact Grothendieck group. The module states this
result and does not prove it.

For a commutative coefficient ring `R`, a group `G` with a topology, any
category `C`, a functor `F : C ⥤ SmoothRep R G`, and a finite list of smooth
functors `P : Fin n → C ⥤ SmoothRep R G`, assume the existing relation

```text
IsGluedFrom (F ⋙ toRep) (fun i => P i ⋙ toRep).
```

For every object `X` such that `F.obj X` has finite group-algebra length,
the proposition asserts the existence of finite-length proofs `hP i` for
every `(P i).obj X`, together with the equality

```text
[F.obj X] = sum i, [(P i).obj X].
```

Every bracket denotes `FiniteLengthGrothendieckGroup.ofRepresentation`
with the corresponding finite-length proof. Thus the formula is in the
exact Grothendieck group of actual smooth representations at the fixed
carrier universe. Its defining relations include all actual short exact
sequences and require no splitting.

## Filtrations and scope

The imported `IsGluedFrom` is defined by a permutation of the finite list
and a zero-to-full filtration by actual natural invariant subspaces.
Each successive quotient is naturally isomorphic to the corresponding
permuted piece. It is not a class equality or an assumption of an
operator identity. Repeated steps and zero graded pieces are permitted.

The statement assumes finite length only of the ambient value `F.obj X`.
It requires the conclusion to supply finite length for every graded
piece: each is isomorphic to a quotient of an invariant subrepresentation
of that value. No simple-factor, irreducibility, admissibility,
finite-dimensionality, or exactness premise on the functors occurs.
The category, coefficient, group, and carrier universes remain explicit
and independent. The group topology is arbitrary; no topological-group
axiom or topology on the coefficient module is required.

The quantifier includes every natural filtration length `n`, including
zero. In the empty case the actual zero-to-full filtration forces the
ambient representation to be zero, and the stated sum is the empty sum.
The proof of that consequence remains part of the proposition.

## Internal provenance and intended use

This is an internal derived statement, not a transcription from original
literature. Its mathematical meaning is determined by the existing
`RepFunctorFiltration`, `HasOrderedFiltration`, and `IsGluedFrom`
definitions in `Filtration.Definitions`, and by the all-short-exact-sequence
quotient in `Smooth.FiniteLengthGrothendieck`.

The intended elementary argument evaluates the filtration at `X`,
applies the exact relation to each adjacent inclusion and quotient,
telescopes from the zero step to the full step, transports each class
through its actual graded isomorphism, and removes the finite permutation.
This paragraph describes a proof obligation; this module implements only
the proposition definition.

The statement neither constructs a geometric-lemma filtration nor proves
induction or Jacquet compatibility, an Aubert identity, or an analytic
classification. Those applications must separately supply the actual
filtration, its natural graded isomorphisms, and finite length of the
ambient value.
