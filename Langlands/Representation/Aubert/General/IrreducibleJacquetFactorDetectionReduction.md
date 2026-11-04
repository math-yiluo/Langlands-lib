# Irreducible Jacquet detection from a cuspidal Jacquet factor

Authors: Worker 658, with the assembly and common-factor routes of Workers 78
and 55. This is an internal conditional reduction for task
`b7887025-20b3-4c11-9fad-0e70bdf59da6`. It does not prove the full rational
irreducible Jacquet detection proposition: its factor-extraction input must
still be supplied by a proved theorem.

`associatedJacquetWitnessOfCuspidalFactors` chooses a standard index `J`
and an actual point `p` which simultaneously supplies association from `I`
to `J`, the displayed Levi membership equivalence under conjugation by
that same `p`, and nontriviality of the actual normalized Jacquet module
`r_J(π)`. The companion theorem
`supportCategoryIrreducibleJacquetDetection_of_cuspidalFactors` proves the
generic `SupportCategoryIrreducibleJacquetDetectionTarget` under the same
four explicit inputs.

## Inputs and scope

The group, its topology, its local compactness and nonarchimedean structure,
and the actual subgroup families and semidirect decompositions are those
of the generic support target. The index, group and carrier universes
`uI`, `uG` and `uV` are independent. Smooth representation carriers have
universe `max uG uV`. No finiteness instance on the index type is used.

The four inputs are:

1. `hfactor`: each irreducible `π` has some nonzero actual normalized Jacquet
   module with an irreducible `IsLeviCuspidal` actual subquotient `τ`.
2. `hextract`: the published proposition template
   `CuspidalJacquetFactorExtractionTarget`, for the same families and
   association relation.
3. `hconjCusp`: transport of the proper-standard inside-Levi cuspidality
   predicate under the supplied association and actual Levi conjugation.
4. `hcomp`: composition of actual association representatives, with
   `I → K` at `n` and `K → J` at `m` giving `I → J` at `m * n`.

The factor `τ` need not realize `π` as a subquotient of its induction.
In particular, this reduction needs no cuspidal induction realization
for the chosen nonzero Jacquet module. It also needs no separate
cuspidal-support association theorem. These statements are conditional
for arbitrary subgroup families: the pair does not assert that any of
the four inputs holds for such families.

## Implemented argument

Fix irreducible `π` in the support category at `I`. Reflexivity of actual
subquotients, proved using `SmoothRep.isSubquotient_iff_exists` and two
identity maps, lets us apply the defining support-category property to
`π` itself. It supplies a standard `K`, an actual point `n`, its Levi
membership equivalence `hn`, an association `I → K`, and an irreducible
cuspidal `σ` on `M_I` such that `π` is an actual subquotient of induction
from `M_K` of `C_n σ`.

The independent input `hfactor` supplies `J`, nontriviality of `r_J(π)`,
and an irreducible cuspidal actual subquotient `τ` of that module.
Irreducibility of `C_n σ` follows from
`Langlands.isIrreducible_comp_continuousMulEquiv_iff` applied to
`conjugationEquiv n hn`; `hconjCusp` supplies its cuspidality.

Apply `hextract` exactly once to `C_n σ`, `π` and `τ`. Its conclusion
gives a point `m`, a Levi membership equivalence `hm`, and association
`K → J` at `m`. Its datum isomorphism is unused. The returned point is
the literal product `p = m * n`. The input `hcomp` proves association
at this point, and transitivity of `hm` with `hn` proves

```text
x ∈ M_J ↔ m⁻¹ * x * m ∈ M_K
        ↔ n⁻¹ * (m⁻¹ * x * m) * n ∈ M_I
        ↔ p⁻¹ * x * p ∈ M_I.
```

The originally selected nontriviality of `r_J(π)` completes the witness.
Classical choice converts its existential construction to a subtype
value. The companion theorem unpacks this value to the generic target.

## Provenance and dependencies

This is internal witness manipulation, adapting Workers 658 and 78's published
`IrreducibleJacquetDetectionReduction` to the cuspidal-factor extraction
interface. It imports that interface and the unchanged rational support
targets by Lean name. It uses actual smooth representations and actual
normalized induction and Jacquet functors throughout.

Besides the definitions named above, the direct proof dependencies are
`conjugationFunctor`, `conjugationEquiv`,
`Langlands.isIrreducible_comp_continuousMulEquiv_iff`, elementary category
identities and group identities. The irreducibility comparison uses the
order isomorphism of invariant-submodule lattices along a continuous
group equivalence; its location in a broader representation module does
not introduce a classification hypothesis.

No classification, character-independence, geometric-lemma, adjointness
or Jacquet-exactness theorem is invoked in this conditional proof.
The extraction and factor-existence inputs carry their own substantive
mathematical obligations; this pair neither proves them nor audits
the proof dependencies of future theorems discharging them.
