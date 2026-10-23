# Contravariant maps between chosen dual parameter schemes

Let `f : A ⟶ B` be an actual abelian-scheme homomorphism over an
arbitrary base `S`, and let `hA : HasDualScheme A` and
`hB : HasDualScheme B` supply universal geometric Picard-zero
families. Under the explicit `HomPicardZeroPullbackStatement`
hypothesis, `dualSchemeMap preservation f hA hB` is a morphism
`dualScheme B hB ⟶ dualScheme A hA` in `Over S`.

It is constructed by pulling back the actual chosen Poincaré family
of `B` along the induced homomorphism on the relative family,
restricting its isomorphism class using the preservation hypothesis,
and classifying that class by the universal family of `A`.
`dualSchemeMap_spec` records the defining equality of classes.
`dualSchemeMapPullbackIso` converts this equality into an actual
rigidified line-bundle isomorphism using `classifyingMap_eq_iff`
and classical choice. No independently chosen scheme morphism or
bundle comparison is assumed.

Under the explicit `RigidifiedModule.PullbackCoherenceStatement`,
`dualSchemeMap_classifies` proves the universal action on classes:
classifying the pullback of any Picard-zero class on `B` is the same
as its classifier on `B` followed by the constructed map. The proof
uses classification uniqueness, composition of parameter pullback,
the defining specification, and the established commutation of
homomorphism pullback with parameter pullback.

`dualSchemeMap_id` applies the identity law for the restricted class
map and the fact that the Poincaré family classifies itself by the
identity. `dualSchemeMap_comp` applies the contravariant composition
law for restricted class pullback and `dualSchemeMap_classifies`.
Thus the identity and composition formulas are proved for these
actual maps, with order reversed under composition.

## Original source and scope

The registered source is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition (6.19), printed p.96 (PDF p.100), characterizes the dual
homomorphism by the isomorphism between the pullback of the Poincaré
bundle of `A` along the dual map and the pullback of that of `B`
along `f`, respecting the unit rigidification. Paragraph (6.2),
printed p.88 (PDF p.92), supplies the universal actual-pullback
formulation. The fibre products here use the parameter-first order
already fixed by `RigidifiedFamily`; `poincareLineBundle` separately
transports to the conventional order.

This is the scheme-map part of that construction, derived over
arbitrary bases from the exact universal-family and preservation
hypotheses. The chosen parameter schemes have not yet been equipped
with their tensor-induced group structures or proved abelian.
Consequently this module does not yet assert that `dualSchemeMap`
is an abelian-scheme homomorphism. Additivity in `f` and extension
to rational homomorphisms also remain separate obligations, in
accord with the distinction in Remark (6.20) on the same source page.
