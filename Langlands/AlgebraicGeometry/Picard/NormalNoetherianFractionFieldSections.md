# Discrete valuative section extension over normal noetherian domains

This internal adapter combines the published discrete valuative
generic-section theorem with the published comparison to a specified
fraction field. Its purpose is to retain the precise field map needed
when working over normal finite models. It introduces no new literature
translation.

`normal_spec_geometricallyUnibranch R` proves that the spectrum of an
integrally closed domain satisfies the Library's geometric-unibranch
condition. The published `spec_hasNormalStalks` gives integral closedness
of each actual structure-sheaf stalk. The published implication from
normal stalks gives the result. This first theorem requires no
noetherianity, valuation or rank condition.

For the remaining results, `R : CommRingCat.{u}` is an integrally closed
noetherian domain and `K : Type u` is any chosen fraction field with its
specified algebra structure. Let `p : X ⟶ Spec R` be separated, locally
of finite type and formally unramified. Assume
`DiscreteValuativeCriterion.Existence p`: every valuative square with
a discrete valuation ring admits a lift.

`fractionFieldSectionRestriction_bijective_of_normal_discreteValuativeExistence`
proves bijectivity of restriction along the exact map
`Spec.map (CommRingCat.ofHom (algebraMap R K))`. Separatedness gives
injectivity. The published discrete generic-section theorem applies to
the noetherian spectrum with its proved geometric-unibranch condition.
The published equivalence between surjectivity for generic residue-field
maps and for chosen-fraction-field maps gives surjectivity here.
No full arbitrary-valuation criterion or separate closed-image
hypothesis is assumed.

`normalNoetherianFractionFieldSectionEquiv` packages the bijection
between actual sections of `p` and actual maps `Spec K ⟶ X` over the
given fraction-field map. Its application lemma identifies the forward
function with the existing `fractionFieldSectionRestriction`.

`existsUnique_fractionFieldSectionExtension_of_normal_discreteValuativeExistence`
unpacks surjectivity into a unique actual morphism `s : Spec R ⟶ X`.
It proves both `s ≫ p = 𝟙 (Spec R)` and the equality of the restriction
of `s` along the unchanged fraction-field map with the prescribed map
`sK`. Injectivity of restriction and subtype extensionality prove
uniqueness.

All universes are the arbitrary common universe `u`. In particular,
the section-extension conclusions retain their noetherianity and
discrete valuative existence hypotheses. This adapter constructs no
correspondence representer, supplies no line-bundle interpretation of
sections, and proves no bundle-extension theorem. Those additional
steps remain necessary for the host two-axis extension statement.
