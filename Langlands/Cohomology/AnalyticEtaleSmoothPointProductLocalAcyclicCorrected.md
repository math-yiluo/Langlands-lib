# Local higher direct images of actual smooth point products, for a topological group

## What this replaces and why

`AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement` replaces the
Library proposition `AnalyticEtaleSmoothPointProductLocalAcyclicStatement` in
`Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclic`. The old
module declares `[IsTopologicalGroup G]` as a section variable. A definition
keeps a section variable only if its body or type uses it, and the old body
does not use this one. Lean therefore left it out, and the elaborated old
proposition is stated for every group `G` with an arbitrary topology. The
source and the task that requested the statement both have a topological
group, so the omission was an oversight. It does not express a wider theorem.

Here `[IsTopologicalGroup G]` is a binder of the definition itself, and a binder
written on the declaration is kept even though the body does not use it. The
smallness and admissible-refinement hypotheses are also written on the
definition. All other hypotheses are unchanged, and so are the explicit argument
order `L X h R G ρ`, the universes, the premises and the conclusion. The only
change is the added instance argument. The corrected proposition has one more
hypothesis than the old one, so it is the weaker of the two.

The old proposition stays in the Library, unproved, and its Markdown is marked
as superseded. It is not to be used as a target or as a premise. Its only
Library consumer was the conditional theorem
`analyticEtaleGodementCompactAcyclic_of_local_and_ordinary`. This module
provides the counterpart
`analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary`, which
takes the corrected proposition and needs a topological group.

## The statement

The definition binds a complete ultrametric ground field `K`, a normed
extension field `L`, an actual analytic object `X`, point axioms `h` for all
`L`-valued points of `X`, and a commutative coefficient ring `R` in
`W = max u (v + 1) uL`. It also binds a group `G` with a topology, an action
`ρ : G →* Aut X`, and the instance arguments `[IsTopologicalGroup G]`,
`[Small.{W} G]` and admissible refinements of the distinguished lift system for
the twisted étale topology. The universes `u`, `v`, `uL` and `z` stay
independent.

Suppose the underlying analytic space is Hausdorff, the actual field-point
projection `pointProjection L X` is surjective, and the action is continuous.
Then for every injective module diagram `N` on the discrete category of
`ULift.{W}` of the actual `L`-valued points, and every `q : ℕ`, the
`q+1`-st ordinary higher direct image `etaleUnderlyingHigherDirectImage X R (q+1)`
of `(etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N` is zero.
This functor is the existing point product followed by the actual induction,
the locally discrete coreflector, the inclusion and the ordinary étale
restriction. The higher direct image is the right-derived functor of the actual
ordinary-open direct image `etaleUnderlyingSheaf`. The statement is not about the
raw point product or about a newly defined soft-sheaf predicate.

## Provenance

This is an internal prerequisite for the Library's actual construction, not a
verbatim statement of a source. Its motivation is the local vanishing condition
(1′) in the proof of Proposition 1.5.1 of Berkovich, *Étale equivariant sheaves on
p-adic analytic spaces* (unfinished 1995–1996 manuscript), printed pages 10–11,
where `G` is a topological group acting continuously. That argument uses finite
Galois neighbourhoods, shrinks the acting group to an open subgroup, and uses
products of coinduced finite Galois modules. No equivalence with local Galois
stalk cohomology is asserted here, and no such comparison is assumed proved. The
retained source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
publication-folder fingerprint
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, file
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

## The conditional consumer

`analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary` assumes the
corrected local statement. It also assumes that the positive ordinary compact
cohomology of the same point-product images vanishes for injective coefficient
diagrams. From these it proves the published Godement compact-acyclicity target
`AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ`, which itself binds
`[IsTopologicalGroup G]`. The proof is the one of the old consumer. The actual
ordinary/étale compact-support comparison
`isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic` gives étale
compact vanishing for the point-product images. The proved coefficient
resolution reduction `analyticEtaleGodementCompactAcyclic_of_injectiveCoefficients`
extends this to every input étale `G`-sheaf.

The theorem uses neither equivariant compact/global comparison, nor the parent
restricted-injective acyclicity, nor preservation of injectives by equivariant
restriction. It does not discharge the local statement or the ordinary compact
vanishing premise.
