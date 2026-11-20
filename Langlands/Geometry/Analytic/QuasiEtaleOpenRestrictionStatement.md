# Statement: quasi-étale morphisms restrict to quasi-étale morphisms over open domains

Author: Worker 5254.

This module states, without proof, that the restriction of a quasi-étale
morphism over an open subset of its target is quasi-étale. It contains one
Prop-valued definition,
`Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleOpenRestrictionStatement`.

## The statement

`QuasiEtaleOpenRestrictionStatement : Prop` (universes `u v`). Let
`K : Type u` be a complete ultrametric normed field and
`f : Y ⟶ Z` a morphism of `LocalizedCategory.{u, v, v}` whose source has a
Hausdorff underlying space (`T2Space (localizedSpaceFunctor.obj Y)`). Assume
`quasiEtale f` (module `QuasiEtaleSite`). Let `V` be an open subset of the
underlying space of `Z`. Then the restriction

`domainRestrict D_Y D_Z f _ : domainObj Y D_Y ⟶ domainObj Z D_Z`

is quasi-étale, where `D_Z = (presentationOf Z).openDomain V hV` is the open
domain `V` of `Z` and `D_Y` is the open domain `f⁻¹(V)` of `Y`. Here
`domainRestrict` (module `InvariantAnalyticDomains`) is the unique morphism
between the domains that commutes with `f` and the canonical morphisms.

## Original source and provenance

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
539–571, registered as `berkovich-1994-vanishing-cycles-formal-schemes`,
Lemma 3.1(i), printed p.544: "Quasi-étale morphisms are preserved under
compositions, under any base change functor and under any ground field
extension functor."

Provenance: derived. The statement is the special case of base change along
the open immersion `V → Z`, where the base change of `f` is its restriction
`f⁻¹(V) → V`. It is formulated with the Library's open domains and
`domainRestrict`. The hypothesis that the source is Hausdorff is added. The
Library's `quasiEtale` asks for neighbourhoods made of charts of the saturated
presentation, and this reading agrees with Berkovich's affinoid domains for
Hausdorff spaces (module `QuasiEtaleSite`, derived choice 1). A proof of the
restriction refines affinoid domains of `Y` near points of `f⁻¹(V)` to charts
of the open domain `f⁻¹(V)`, and this uses that agreement. The statement is
used only for Hausdorff sources. With the extra hypothesis it is weaker than
the statement without it.

## Role

This statement is a prerequisite for the proof of Berkovich's Example
1.2.1(i) (`QuasiEtaleSiteEquivalenceStatement`, Task 5695). The quasi-inverse
of induction sends a quasi-étale `G`-space `W → X_{G/H}` to its part over the
copy of `X` indexed by the coset `H`. That part is the restriction of `W → X_{G/H}` over this open copy, so it is quasi-étale by this statement.

## Scope

This is a `lean.statement`: nothing is proved here.
