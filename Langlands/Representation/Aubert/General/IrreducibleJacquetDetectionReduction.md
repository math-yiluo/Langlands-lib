# Irreducible Jacquet detection from explicit cuspidal inputs

This internal construction assembles an associated nonzero Jacquet witness from
four explicit mathematical inputs. It concerns the published generic standard
families and actual normalized functors of
`Langlands.Aubert.General.SupportCategoryStatements`. It is a conditional
reduction, and does not prove the rational-point detection statement by itself.

The group has an arbitrary universe `uG`, the index type an independent universe
`uI`, and the representation carriers have universe `max uG uV`, with `uV`
independent. The group is locally compact and nonarchimedean. The standard
parabolic, Levi and unipotent subgroups, their ambient and inside-Levi
semidirect decompositions, and the closedness assumptions are exactly the data
of the imported generic target. There is no finiteness assumption on the index
type.

`associatedJacquetWitnessOfCuspidalRealizations` constructs a pair `(J, g)` with
three certificates: `IsAssociate I J g`, the displayed conjugation membership
equivalence from `M I` to `M J` for the same `g`, and nontriviality of the actual
normalized Jacquet module of `π` at `J`. Its four inputs are:

1. `hrealize`: every irreducible `π` is an actual subquotient of normalized
   induction from an irreducible Levi-cuspidal `τ` at some `J` for which
   `r_J(π)` is nontrivial. This requires the induction realization and nonzero
   Jacquet module at the same `J`.
2. `hassoc`: the entire published `CuspidalSupportAssociationTarget`, including
   its representative-specific root-association, Levi-membership and
   representation-isomorphism conclusions.
3. `hconjCusp`: transport of proper-standard Levi cuspidality by the actual
   conjugation functor whenever the same point satisfies the association and
   Levi-membership conditions.
4. `hcomp`: the representative-specific law that association from `I` to `K`
   through `n` followed by association from `K` to `J` through `m` gives
   association from `I` to `J` through the literal product `m * n`.

The implementation applies support-category membership to the irreducible
representation itself. The published `SmoothRep.isSubquotient_iff_exists`
gives this self-subquotient presentation from two identity morphisms. This gives `K`,
`n`, and an irreducible cuspidal `σ` at `I`, with `π` a subquotient of induction
from its conjugate at `K`. Irreducibility of the conjugate follows from the
published `Langlands.isIrreducible_comp_continuousMulEquiv_iff` applied to
`conjugationEquiv n hn`; its cuspidality follows from `hconjCusp`. Applying
`hassoc` to this realization and the one supplied by `hrealize` gives an actual
point `m` associating `K` to `J`. The representation isomorphism in this
association conclusion is not needed for this construction.

The output point is `m * n`. Its root-association certificate uses `hcomp`.
Its Levi-membership certificate composes the two supplied equivalences

```
x ∈ M J ↔ m⁻¹ * x * m ∈ M K
        ↔ n⁻¹ * (m⁻¹ * x * m) * n ∈ M I.
```

The inverse-of-product identity and associativity identify the last expression
with `(m * n)⁻¹ * x * (m * n) ∈ M I`. The nonzero Jacquet certificate is the one
from `hrealize`, unchanged. Classical choice selects this certified pair.

`supportCategoryIrreducibleJacquetDetection_of_cuspidalRealizations` projects the
constructed pair to prove exactly the generic
`SupportCategoryIrreducibleJacquetDetectionTarget`, under the same four inputs.
Neither declaration assumes finite length, admissibility, finite generation,
compactness or compact-limit conditions. The substantial realization,
association and transport inputs remain explicit proof obligations in any
application. In particular, existence of a cuspidal series alone, or of a
nonzero cuspidal Jacquet module alone, does not supply `hrealize`.

This is internal logical assembly from the imported definitions, the
subquotient presentation theorem, irreducibility under continuous group
equivalence, and elementary group identities. Its proof body uses no
classification, character independence, geometric lemma or adjointness theorem.
The mathematical contents and dependencies of any future proofs supplying the
four inputs must be recorded separately. The only direct import is
`Langlands.Representation.Aubert.General.SupportCategoryStatements`; the
existing support definitions and targets are preserved.
