# Section representations of actual small-etale transport sheaves

This internal extension of `EtaleTransportSite` takes a scheme `Y` in
universe `u`, a group `G` in an independent universe `w`, and the actual
action `ρ : G →* (Aut Y)ᵐᵒᵖ`. It constructs global section actions directly
from the genuine labelled scheme maps. It does not assume a cohomology
object or a desired comparison.

`whole ρ` is the identity etale map of `Y`. `wholeIsTerminal` proves that
its ordinary etale object is terminal, using the structure map from each
etale object and the defining commutative triangle for uniqueness. This
terminal assertion concerns the ordinary etale category. `wholeMap ρ g`
is the transport endomorphism labelled `g` with underlying scheme map
`(EtaleCohomologyAction.aut ρ g).hom`. Its identity and multiplication
laws retain both the group label and the scheme map.

For any coefficient category `A` with independent object and morphism
universes, `evaluation ρ A U` evaluates the actual sheaf at `U`.
`sectionAction ρ A` evaluates at `whole ρ` and lets `g` act by the
presheaf restriction along `(wholeMap ρ g).op`. Since
`wholeMap (g*h) = wholeMap g ≫ wholeMap h`, contravariance gives the
product law in the categorical endomorphism monoid. A morphism acts
by its whole-scheme component, and its naturality is exactly the
intertwining equation. The exposed component formulas describe these
maps. `sectionActionForgetIso` and `evaluationToSheafIso` identify the
underlying sections with whole-scheme evaluation and ordinary etale
sheaf evaluation, respectively.

Evaluation preserves every limit shape available in `A`, since the
sheaf-to-presheaf inclusion creates these limits and presheaf limits
are pointwise. `toSheaf_preservesLimitsOfShape` proves the corresponding
statement for ordinary restriction: its composite with the ordinary
sheaf inclusion is presheaf restriction, which preserves those limits;
the ordinary inclusion reflects limits. Both functors therefore preserve
finite limits when `A` has them.

For a commutative ring `R` in an independent universe `uR` and module
carriers in another universe `uM`, `ModuleSheaf ρ R` is the actual category
of module-valued transport sheaves. `sectionRepresentation ρ R` converts
the constructed section action using Mathlib's `Rep.ActionToRep`.
It is additive by componentwise addition and preserves finite limits
because the faithful representation forgetful functor reflects limits.
`sectionRepresentationForgetIso` identifies its forgotten functor with
whole-scheme evaluation. In the ordinary coefficient scope `R : Type u`,
with carriers in `u`, `sectionRepresentationOrdinaryIso` compares it with
`toSheaf ρ (ModuleCat R)` followed by the existing ordinary etale global
sections. The latter isomorphism uses the canonical global-sections versus
terminal-evaluation comparison for `wholeIsTerminal`.

`sectionComplex ρ R c` applies this additive functor termwise to any
supplied strict complex, for any complex shape `c`. Thus every differential
is an actual intertwiner and its square is zero. Functorial chain maps
come from the actual sheaf chain maps. `sectionComplexForgetIso` is the
natural comparison between its underlying module complex and the
whole-scheme evaluation complex, obtained by the standard comparison
for applying composable additive functors to complexes.

The existing ordinary-topological `FunctionSheaf.sectionRepresentation`,
`EquivariantDerivedSections.sectionRepresentationForgetIso`, and
`EquivariantSections.globalComplex` supply the assembly method. Here
the action arrows are actual scheme automorphisms in the new etale
transport category, with the opposite-automorphism convention above.
This is a derived internal construction, with no new literature claim.
No group topology, faithfulness, finiteness or equality of the scheme,
group, ring and module-carrier universes is imposed. These are algebraic
representations and termwise sections of supplied complexes. Abelian
structure, sheafification and enough injectives in the small coefficient
universe, computation of ordinary etale derived sections after forgetting,
derived representation-valued sections, smoothness, supports and Harris
arithmetic specialization remain separate obligations.
