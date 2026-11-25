# Local higher direct images of actual smooth point products

> **Superseded; do not use as a target or as a premise.**
> `AnalyticEtaleSmoothPointProductLocalAcyclicStatement` was stated without the
> group-topology hypothesis by oversight. The module declares
> `[IsTopologicalGroup G]` as a section variable, but the body of the definition
> does not use it, so Lean leaves it out of the definition. The elaborated
> proposition therefore quantifies over every group `G` with an arbitrary
> topology. The intended setting, that of the source, is a topological group.
> The proposition stays in the
> Library unproved.
>
> It is replaced by
> `AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement` in
> `Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclicCorrected`.
> That definition has the same body, with `[IsTopologicalGroup G]`,
> `[Small.{max u (v + 1) uL} G]` and the admissible-refinement hypothesis bound
> on the definition itself. Because it has the extra hypothesis, the corrected
> proposition is the weaker one. A consumer of the old proposition must move to
> the corrected one and must supply a topological group. The consumer
> `analyticEtaleGodementCompactAcyclic_of_local_and_ordinary` below has the
> counterpart `analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary`
> in the corrected module, with the same conclusion and ordinary premise.
>
> The rest of this page describes the original module as it was published. Its
> description of the hypotheses omits the topological-group hypothesis for the
> reason above.

`AnalyticEtaleSmoothPointProductLocalAcyclicStatement` is an unproved internal
analytic prerequisite for Godement compact acyclicity. It retains the complete
ultrametric ground field `K`, normed extension field `L`, actual analytic object
`X`, supplied point axioms `h`, actual group action `ρ`, and independent universe
levels `u`, `v`, `uL` and `z`. Set `W = max u (v + 1) uL`. The coefficients use
`W`, the group is small in `W`, and its distinguished lift system has admissible
refinements.

Under Hausdorffness of the underlying analytic space, surjectivity of the actual
field-point projection and continuity of the action, the statement quantifies
over every injective module diagram on the discrete category of
`ULift.{W}` of the actual `L`-valued points, and every `q : ℕ`. It asserts the
`q+1` ordinary higher direct image of its image under
`etaleCoefficientRestrictedSmoothPointProductFunctor` is zero. This is exactly
the existing point product, actual induction, locally discrete coreflector,
inclusion and ordinary étale restriction. The higher direct image is exactly
`etaleUnderlyingHigherDirectImage`, the right-derived functor of actual
ordinary-open direct image `etaleUnderlyingSheaf`. Thus the input is not replaced
by the raw point product or a newly defined soft-sheaf predicate.

The intended analytic motivation is the local vanishing condition (1′) in the
proof of Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished 1995–1996 manuscript), Proposition 1.5.1, printed pages 10–11. In
that argument finite Galois neighborhoods, shrinking the acting group to an
open subgroup, and products of coinduced finite Galois modules establish local
Galois acyclicity. The present right-derived ordinary-direct-image formulation
is an internal prerequisite for the Library's actual construction, not a verbatim
statement of that source. No equivalence with local Galois stalk cohomology is
asserted here, and no such comparison is assumed proved. The retained source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
whose registered publication-folder fingerprint is
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The cited file is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The manuscript's printed pages 10–12 were read for this formulation.

`analyticEtaleGodementCompactAcyclic_of_local_and_ordinary` proves a conditional
connection to the exact published Godement compact-acyclicity target. In addition
to the local input it explicitly assumes positive ordinary compact cohomology of
the same point-product images is zero for injective coefficient diagrams. The
actual ordinary/étale compact-support comparison
`isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic` then gives actual
étale compact vanishing for those images. The proved coefficient resolution
reduction and actual Godement natural isomorphism extend this to every input
étale `G`-sheaf, with no injectivity requirement on that final input.

The conditional theorem uses neither equivariant compact/global comparison,
parent restricted-injective acyclicity nor injectivity preservation by
equivariant restriction. Neither the local statement nor the ordinary compact
vanishing premise is discharged by this module. Raw point-product acyclicity alone
cannot justify passing through the locally discrete coreflector.
