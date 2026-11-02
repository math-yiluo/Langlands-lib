# Renard II.2.1: direct gluing and the chosen-basis and all-open germ sheaves

Worker 633 implemented the direct gluing and categorical packaging. Worker 6
contributed the original-source audit and the suggested pointwise gluing route.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, printed pp.34–35 / PDF pp.40–41,
equation (II.2.1.2), the ensuing direct sheaf and morphism constructions, and
printed p.37 / PDF p.43 for the same section families on all opens. These
pages were read in full, with PDF p.40 visually checked. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary registered 2010-edition corrections,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were also read. Their index corrections do not alter the carrier
or direct gluing construction.

The imported `GermSections` supplies the actual subgroup of dependent families
`(x : U) → rawStalk F x.val` represented by original sections on whole
contained basis neighborhoods. This is the fiber-respecting presentation of
sections in the disjoint stalk union. No topology on that union or original
stalk representative/equality characterization is used.

`germPresheafOn C F` evaluates precisely these groups on the actual opens of
an auxiliary target basis `C`. The stalks and local original representatives
always come from the original input basis `B`; changing `C` never reconstructs
stalks. Its maps are the actual additive `germRestriction` maps from the
imported module. Identity and composition are their intrinsic laws, and its
empty values are subsingleton because the family domain is empty.

The gluing proof follows the direct route of printed p.35. Literal
compatibility compares restrictions on every smaller target basis open
inside an overlap. `compatible_germSections_value` refines the overlap at a
point using `C.exists_subset` and evaluates that compatibility equality there.
Thus the values of any two cover sections agree at that point.
`germGlueFamily` chooses a member containing each point and uses its value.
`germGlueFamily_eq` proves independence from that choice with the overlap
argument. `germGlueFamily_locallyRepresented` takes an original local
representative from a chosen cover section. Its neighborhood lies inside
the covered open, and choice independence identifies the representative's
germs with the glued values throughout that neighborhood. This constructs
the actual `germGlue` section. Its restriction to each cover member is the
given section by pointwise equality.

`germPresheafOn_familySheafCondition` proves uniqueness by choosing a cover
member at each point and evaluating an alleged amalgamation's restriction
there. It permits an independent cover-index universe `w`. In particular it
gives the existing literal `SheafCondition` by its published family-to-set
API. `germNormalizedPresheafOn` and `germSheafOn` bundle the actual normalized
presheaf and literal `BasisSheaf`; no sheaf property of the original input is
assumed. Empty domains and empty covers require no choice at a point, since
there are no domain points. The arguments do not require empty to belong to
either chosen basis.

`germPresheafMapOn` uses the pointwise additive stalk map and its restriction
law. `rawGermSheafFunctorOn` bundles the resulting natural transformation in
the two existing full subcategories; identity and composition are checked
componentwise using the imported stalk-family laws. Specializing `C = B`
gives `rawGermSheafFunctor`. The source-normalized functor
`germSheafFunctor` is its composition with the actual `presheafInclusion`.

`allOpenBasis` is the canonical `OpenBasis X` of all actual opens, with the
supplied topology preserved. `allOpen` gives its object for any actual open.
`rawAllOpenGermSheafFunctor` specializes the same auxiliary construction to
this basis, and `allOpenGermSheafFunctor` again uses the actual normalized
inclusion. The exposed evaluation, restriction and component-map equalities
are definitional: both packagings use the same `GermSections F U`,
`germRestriction F h` and `germSectionsMap φ U`.

The raw-input extension and the categorical packaging in value universe
`max u v` are internal extensions that specialize to Renard's normalized
construction. The space universe `u` and original value universe `v` are
independent, without a universe comparison or a same-value-universe
adjunction assertion. The auxiliary target-basis parameter is internal
reuse of the same direct proof, not an asserted equivalence of sheaf
categories. No separation, intersection closure, local compactness,
countability, global nonemptiness or nontriviality hypothesis is imposed.
The original stalk quotient description, etale-space topology,
sheafification unit and adjunction, unit isomorphism on sheaves,
basis/all-open equivalence, and support constructions remain separate.
