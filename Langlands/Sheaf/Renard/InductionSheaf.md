# Renard III.3.2: the actual induction sheaf

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, III.3.2, printed pp.84–85 / PDF pp.90–91, the
construction of the functor `I_H^G` by applying the II.2.5 inverse sheaf functor
to the nondegenerate pointwise test module `ind_H^G E`. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All declarations are in `Langlands.Sheaf.Renard.InductionSheaf`.

The group `G : Type` is a topological group with explicit
`hG : IsLocallyProfinite G`, retaining Hausdorffness and the compact-open
neighbourhood basis. `H` is the actual subgroup, with explicit closedness
`hH`. Coefficients and their carriers are the original universe-zero complex
vector spaces. The source is the existing `Langlands.SmoothRep ℂ H` category.
The target is the existing `SectionActions.SmoothActionSheaf` category on the
original `Langlands.Induction.LeftQuotient H`. Its action is exactly
`HomogeneousSections.homogeneousAction`, `g₀ • Hg = H(g g₀⁻¹)`.
The published quotient result supplies the Hausdorff compact-open basis of
this actual quotient. Local compactness of `G` is obtained from `hG` wherever
the original compact-induction module construction requires its instance.

`compactCompatible_smooth` uses the existing `compactInduced_smooth`: the
whole original compact-induced representation is smooth by its uniform open
right stabilizers. The canonical complex action in
`CompactInductionTestModule` has those same operators on that same carrier,
so its smoothness predicate reduces to the original one. No smooth-vector
subspace is substituted here.

`compatibleInduction` lifts the published
`CompactInductionTestModule.functor G H hH` into the existing smooth compatible
test-action full subcategory. That functor uses the original
`CompactFunctions H σ`, the pointwise quotient-test multiplication, and the
original induced maps. Its complex structure is the canonical one proved to
agree with the original compact-induced structure.

`functor hG H hH` is the actual `I_H^G`. It forgets the source representation's
smoothness proof, applies this original compact-induction compatible-module
functor, and applies `SmoothProjectorActionSheaf.smoothFunctor` to the original
quotient. This is the II.2.5 projector sheaf equipped with the constructed
inverse-labelled module action; its full compact-section representation is
smooth by the actual reconstruction result.

`toActionIso` records that forgetting smoothness gives exactly the composite
of the original compact-induced test-module functor with the original
equivariant projector-sheaf functor. It is an identity natural isomorphism.
`underlyingSheafIso A` records the ordinary vector sheaf as the published
`ProjectorVectorSheaf.sheaf` of the actual compact-induced test module, with
the identity maps on all compatible families.

This construction is on the literal homogeneous quotient and requires no
transitive-space identification. Renard uses countability at infinity to
identify an arbitrary transitive action space with a quotient; that
identification and its sigma-compactness hypothesis remain separate. The
fibre-at-origin comparison with the original H-representation, the compact
and smooth-global section isomorphisms, their explicit inverse beta, and the
homogeneous categorical equivalence are not asserted here. They remain
statements over these actual functors and maps, followed by separate proof
tasks. No II.2.5 comparison is assumed invertible in this construction.
