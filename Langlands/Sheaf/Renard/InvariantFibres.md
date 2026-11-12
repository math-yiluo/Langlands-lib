# Original invariant fibres and their actual sheaf restrictions

This construction supplies the literal fibre objects used in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.3.1 Proposition and Corollary, printed pp.83–84 / PDF
pp.89–90. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original pages were read directly. The construction uses the published
actual inverse-image infrastructure; it does not state or prove the fibre
coinvariant comparison.

All declarations have prefix `Langlands.Sheaf.Renard.InvariantFibres`.
The group, base spaces, complex coefficients, section and quotient carriers
are universe zero, as required by the published actual inverse-image and
compact-support interfaces. `G` has a topology and acts jointly continuously
on `X`. The actual continuous map `q : C(X,Y)` and its actual invariance
`hq : ∀ g x, q(g • x)=q x` are inputs. No smoothness, properness,
surjectivity or transitivity is assumed.

`Fibre q y` is literally `{x : X // q x=y}` with its actual subtype topology.
`fibreAction` uses the original action on the underlying point; invariance
of `q` proves that it stays in this same subtype. Its identity and product
laws are the original action laws, by subtype extensionality.
`fibreContinuousSMul` uses the original joint continuity and the subtype
inclusion. These structures are passed explicitly to the following
constructions; no competing action is inferred.

`inclusion q y` is the actual continuous subtype inclusion. If `Y` is
Hausdorff, `fibre_closed` is closedness of the preimage of the singleton.
With explicit `IsLocallyProfinite` predicates on `X` and `Y`,
`fibre_isLocallyProfinite` applies the published locally closed subspace
result to this same closed subtype. It retains Hausdorffness and the
compact-open neighbourhood basis, and includes empty fibres.

`restriction q hq y` is the existing `SectionActions.actionInverseImage`
along the actual inclusion with its literal equivariance equation. It uses
the original transport-site Kan extension and sheafification on every
original action sheaf and sheaf map. `restrictionToSheafIso` specializes
the published ordinary inverse-image comparison: forgetting the action
gives ordinary sheaf restriction to exactly that subtype. No assumed
fibre comparison or substitute sheaf occurs.

`compactSections q hq y` composes this actual restriction with the existing
`CompactSections.functor`. It therefore takes all original compactly
supported global sections of the restriction, with their original group
operators, even when the ambient action sheaf is not smooth.

`representationCoinvariants` abbreviates the existing
`Rep.coinvariantsFunctor ℂ G`, whose objects and maps are the original
`Representation.Coinvariants` and `Representation.Coinvariants.map`.
It retains the actual quotient and its induced maps. `coinvariants q hq y` composes this with
`compactSections`: these are exactly the vector spaces
`F_c(q⁻¹{y})_G`, naturally in the original equivariant sheaf.

The source's compact restriction surjectivity and kernel description, the
natural comparison with the coinvariant sheaf's original stalk and the
distribution Corollary remain statements and proof obligations. None is
assumed or proved in this construction.
