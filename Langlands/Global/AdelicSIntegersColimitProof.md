# Proof of the actual integer-ring colimits

Authors: Worker 208 (complete proof draft); Worker 1566 (source and
interface verification, explanatory Markdown and submission preparation).

The theorem `Langlands.Global.adelicSIntegersColimit` proves exactly
`Langlands.Global.AdelicSIntegersColimitStatement`, in an arbitrary common
universe. Its source is Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed p.6, Remark 3.5. The statement
and its Markdown explain the derived perfect-constant-field and empty-S
scope. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof retains all the statement's field, scalar-tower and
function-field hypotheses; it introduces no separability hypothesis.
The constant field may be any perfect field. Every finite initial S,
including the empty set, is allowed in both arithmetic branches.

For function fields, `exists_mem_curvePlaceSIntegersAbove` uses the
published finite-poles exhaustion `exists_mem_curvePlaceSIntegers`
and then adjoins the prescribed initial finite set S. For number fields,
`exists_mem_numberFieldSIntegers` uses Mathlib's
`IsDedekindDomain.HeightOneSpectrum.Support.finite` for the original ring
of integers. Outside that finite support, failure of the strict
inequality above one gives the required valuation bound. Enlarging the
support by S proves `exists_mem_numberFieldSIntegersAbove`. The
auxiliary monotonicity lemma expresses the literal weakening of
outside-set integrality.

In each branch, `SubringCover.desc` constructs a ring homomorphism from
the original field into the vertex of any compatible cocone. Its cover
uses the actual integer subrings at S union T. The compatibility
equations are the cocone's naturality equations. Its restriction to an
arbitrary stage is proved by enlarging that stage once more and using
the same naturality equation.

The restriction formula at the initial stage shows that the descended
map preserves the original S-integer scalar action. Thus it is an
algebra morphism over the original base. The restriction formula gives
the factorization equations, and exhaustion gives uniqueness by
evaluating any competing algebra map at a stage containing the chosen
field element. These supply `IsColimit` witnesses for the literal
field-valued cocones, with the original fields as their vertices.

The final theorem combines these witnesses with the two exhaustion
results. The proof reuses the published directed-subring-cover
construction from `FiniteAdeleLevelColimitProof`. It makes no assertion
about scheme limits, existence of arithmetic spreads, topologies, or
independence of arbitrary spreads.
