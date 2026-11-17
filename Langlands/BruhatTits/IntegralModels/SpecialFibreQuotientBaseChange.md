# Generic coefficient base change of actual reductive special-fibre quotients

This internal provider moves the published theorem
`SpecialFibreQuotientData.isReductiveQuotient_baseChange` from
`UnramifiedFacetSignDescent`. Its name, type and proof body are unchanged.
The two private instances used in its proof move with it. The former module
imports this provider, preserving the theorem for its existing consumers.
The new proposition `SpecialFibreQuotientBaseChangeStatement` records the same
generic result, and `specialFibreQuotientBaseChange` proves it by applying that
theorem. No independent literature assertion is added.

Work in arbitrary universe `u`. Supply local domains `R` and `A` with a local
algebra map, fraction fields `K` and `L`, and compatible scalar towers through
both `A` and `K`. Supply a group scheme `G` over `K`, relative component model
data `D` over `R` for `G`, and actual special-fibre quotient data `Q` for `D`.
Assume the induced residue-field extension is separable and algebraic.
The statement says that `Q.IsReductiveQuotient` implies
`(Q.baseChange A L).IsReductiveQuotient`. There is no characteristic restriction.

Here `Q.baseChange` is the published construction from
`FacetRootSignBaseChange`. Its radical and quotient are the literal residue
base changes, and the radical inclusion and quotient projection use the
actual `specialFibreSquareIso`. The conclusion retains the full unipotent
radical, fppf quotient and connected reductivity predicate.

The implemented proof first obtains smoothness, affineness and connectedness
of the neutral special fibre from the supplied model data. The published
`separableAlgebraicUnipotentRadical` theorem preserves its unipotent radical
under the residue extension; `IsUnipotentRadical.comp_iso` then changes the
ambient fibre by the coefficient-square isomorphism. Base change of the fppf
quotient followed by `comapIso`, together with the two range identities,
proves the quotient clause. Finally,
`IsConnectedReductive.baseChange_of_algebraicExtension` proves connected
reductivity. These are the original three proof steps.

The accompanying import changes make `RecoveredSpecialFibreQuotient` use this
generic provider and make `UnramifiedRecoveredTorusGeneric` use
`IntegralSplitTorusConversion`. Their declaration types and proof bodies are
unchanged. These imports allow the existing special-apartment chamber proof to
use the providers without the unrelated facet-sign descent interfaces. No
chamber, reference torus or prescribed-point fixation is asserted by this unit.

The same focused import repair relocates the three published induced-residue
arithmetic lemmas into `UnramifiedResidueArithmetic`. That provider's paired
Markdown explains the unchanged proofs and its separate proposition summary.
`UnramifiedFacetSignDescent` imports both generic providers, while
`UnramifiedRecoveredRootRestriction` imports the arithmetic provider directly.
The recovered quotient validity theorem therefore retains its exact existing
proof after the transitive sign-descent import is removed. All relocated lemma
names, types and proof bodies are unchanged.
