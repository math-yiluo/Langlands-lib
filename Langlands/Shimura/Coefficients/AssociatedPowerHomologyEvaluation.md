# Coverwise homology of associated power complexes

This internal construction identifies evaluation of the published diagram
homology systems with homology of their actual complexes at one cover. It
transports their ordinary inverse limits, canonical homology/limit comparisons,
the comparison between the two power systems, and genuine quotient units.
The isomorphisms are constructed from exact evaluation and the universal
property of ordinary limits.

The module reuses
`Langlands.Cohomology.mapHomologicalComplexHomologyIso` from
`Langlands/Cohomology/DivisibleSystem/InverseLimit.lean`. Its generic first
section needs neither a divisible system nor the conditional inverse-limit
theorems later in that file. This contribution does not redefine that general
isomorphism or Mathlib's evaluation criteria for quasi-isomorphisms.

## Parameters and notation

Let `R : Type u` be a commutative ring, `X : Scheme.{u}`, and
`J : Type uJ` a category with morphism universe `vJ`. Put

\[
S=\operatorname{Sheaf}(X_{\mathrm{et}},\operatorname{ModuleCat}_R),
\qquad A=(J\to S).
\]

Here the sheaves are on Mathlib's actual small-etale site of `X`, with module
carrier universe `u`. Let `c : ComplexShape ι`, with `ι : Type uι`, let
`i : ι`, and fix `j : J`. The cover-object, cover-morphism and degree universes
are independent of `u`. Write `H_A` and `H_S` for the actual degree-`i`
homology functors in the abelian categories `A` and `S`. Write `E_j : A ⥤ S`
for evaluation and `E_j^c` for its lift to complexes.

The general constructions use an arbitrary
`F : ℕᵒᵖ ⥤ HomologicalComplex A c`. All limits in this module are over
`ℕᵒᵖ`; there is no limit over `J`. The power index contains every natural
number, including zero. No positivity assumption or truncation is added.

## Evaluation and ordinary limits

`etaleSheafComplexEvaluation X c j` is `E_j^c`. The natural isomorphism
`etaleSheafHomologyEvaluationIso X c i j` has direction

\[
H_A\mathbin{\gg} E_j \;\cong\; E_j^c\mathbin{\gg} H_S
\]

in Lean's left-to-right functor-composition convention: its component at `L`
is `(H_A L).obj j ≅ H_S(E_j^c L)`. Evaluation preserves finite limits and
finite colimits, so it preserves the kernels and cokernels used to construct
homology. The definition is the inverse of the published generic isomorphism.
It is natural in all chain maps of diagram complexes.

`etaleSheafHomologySystemEvaluationIso` whisks this isomorphism by `F`.
Consequently it respects the entire inverse system, including every transition
map. `etaleSheafHomologyLimitEvaluationIso` constructs

\[
(\lim_n H_A(F_n)).obj\,j
  \;\cong\;
\lim_n H_S(E_j^c F_n).
\]

First it uses pointwise limits in the functor category `A`, then the limit of
the preceding natural isomorphism. Its `_hom_π` equation states that projection
at `n` is the evaluated original limit projection followed by the homology
evaluation isomorphism at `F_n`.

`etaleSheafHomologyLimitEvaluationIso_naturality` proves compatibility with
every natural transformation `α : F ⟶ G`. Its right-hand map is the ordinary
limit of the actual maps `H_S(E_j^c(α_n))`. This applies in particular to maps
of coefficient complexes after either published power-system functor.

`etaleSheafLimitHomologyEvaluationIso` gives a second isomorphism

\[
(H_A(\lim_n F_n)).obj\,j
  \;\cong\;
H_S(\lim_n E_j^c F_n).
\]

It composes the homology evaluation isomorphism at `limit F` with homology of
the limit-preservation isomorphism for `E_j^c`. Only evaluation and its lift
preserve the limits used in this construction.

Let `κ_F : H_A(limit F) ⟶ limit(F ⋙ H_A)` be Mathlib's canonical
`limit.post`. Let `e_F` denote the first limit evaluation isomorphism and `s_F`
the second one. `etaleSheafLimitHomologyComparison_evaluation` proves

\[
(\kappa_F).app\,j\;\gg e_F.hom
  =s_F.hom\;\gg\kappa_{F\mathbin{\gg}E_j^c}.
\]

Thus evaluation carries the canonical comparison to the canonical comparison
for the actual coverwise complexes. Neither comparison is asserted to be
invertible.

## Associated coefficient systems and quotient units

The specialization additionally takes an arbitrary ideal `I : Ideal R`,
`D : J ⥤ GrpCat.{u}`, an actual equivariant etale diagram
`Y : EquivariantDiagram D X.Etale`, and
`hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j)`.
The coefficient complex is
`K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c`.
These are the inputs of the published associated-complex construction.

Write `Fˢ_K` for
`(etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K`, the actual
sheaf-power quotient-complex system, and `Fᵃ_K` for
`(etaleAssociatedComplexPowerSystems I X Y hY c).obj K`, the actual associated
coefficient-power quotient-complex system. The two are kept distinct.

- `etaleAssociatedSheafPowerHomologyLimitEvaluationIso` applies `e_F` to
  `Fˢ_K`; `etaleAssociatedPowerHomologyLimitEvaluationIso` applies it to
  `Fᵃ_K`.
- `etaleAssociatedSheafPowerLimitHomologyComparison_evaluation` and
  `etaleAssociatedPowerLimitHomologyComparison_evaluation` specialize the
  canonical comparison square to the two actual systems.
- `etaleAssociatedPowerHomologyLimitComparison_evaluation` specializes
  naturality to the published chain-map comparison `Fˢ_K ⟶ Fᵃ_K`.
  Its right-hand map is the ordinary limit of homology of the evaluated actual
  comparison maps.
- The two `_HomologyLimitUnit_evaluation_projection` lemmas identify the
  published homology units after evaluation, limit identification and projection
  at any `n : ℕ`. For either actual quotient chain map `q_n`, the result is
  `homologyMap (E_j^c.map q_n) i`, preceded by the homology evaluation
  isomorphism for the original associated complex. On the sheaf side `q_n` is
  `sheafDiagramComplexPowerUnit`; on the coefficient side it is association
  applied to `coefficientComplexPowerUnit`. No arbitrary replacement quotient
  map is supplied.

## Implemented proofs and provenance

This is a derived internal interface for the published constructions in
`AssociatedPowerHomology`, `AssociatedPowerComplexComparison`,
`SheafDiagramAdicComplex` and `AssociatedComplex`. It makes no new claim of
translation from original literature.

The general homology isomorphism reuses the generic construction cited above,
which uses Mathlib's `ShortComplex.mapHomologyIso`. Exactness of evaluation
comes from the pointwise abelian structure and limit/colimit preservation in
Mathlib. Ordinary-limit evaluation uses
`limitObjIsoLimitCompEvaluation`, `HasLimit.isoOfNatIso` and
`preservesLimitIso`. Projection equations use their existing projection
identities. Naturality and the canonical comparison square follow by
`limit.hom_ext`, projection identities and naturality of the homology evaluation
isomorphism. The specialized squares directly apply those results. The
quotient-unit formulas use the published genuine quotient projection equations
and the same naturality. These proofs construct all intrinsic fields and
equations without new axioms or assumed comparison maps.

## Scope

Homology is in the category of small-etale module sheaves or its diagram
category. Evaluation here means a coordinate of the cover diagram; it is not
evaluation of a sheaf on an etale object or a global-section functor. All
inverse limits are ordinary. The module proves no infinite-limit preservation
by homology, Mittag-Leffler or finiteness result, invertibility of either
canonical homology/limit map, exactness of associated sheaves, derived
completion or derived/global cohomology comparison. Continuous or smooth
actions, lisse-adic properties, and the actual Harris scheme, cover tower and
coefficient specialization remain separate obligations.
