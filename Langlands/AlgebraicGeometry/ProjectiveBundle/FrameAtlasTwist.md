# Degree-one bundles across genuine frame atlases

This derived unit constructs degree-one line bundles on the actual projective
schemes made from different bases of frame-bearing opens. It uses the published
`FrameAtlas` comparisons, the fixed `FrameBundle` degree-one bundle, and canonical
module-sheaf pullback comparisons. No additional geometric assertion from an
external source is invoked.

Let `S : Scheme.{u}`, `M : S.Modules`, and `n : ℕ`. Each `a : FrameAtlas M n`
specifies a topological basis of opens and a genuine frame of `M` on every
basis member. Assume `hM : IsLocallyFreeOfRank M (n + 1)`. The existing
`a.bundle` is the actual glued projective scheme. Write

- `P_a = a.bundle`;
- `t_a = (a.toFrameBundleIso hM).hom`;
- `f_ab = (a.comparisonIso hM b).hom`;
- `N = (FrameBundle.twistOne hM).obj`.

## Actual line bundles and comparisons

`twistOne hM` has underlying module `t_a^* N`. Its local rank-one property
follows from preservation of local rank one by pullback. It therefore defines
an actual line bundle on `P_a`.

`comparisonIso_hom_toFrameBundle` proves `f_ab ≫ t_b = t_a` by cancellation
in the defining composition of the two scheme isomorphisms.
`comparisonIso_hom_comp` extracts `f_ab ≫ f_bc = f_ac` from the published
`comparisonIso_trans`.

`comparisonTwistIso hM b` is the canonical composition isomorphism

`f_ab^* (t_b^* N) ≅ t_a^* N`.

`comparisonTwistLineIso` lifts it to an isomorphism of line bundles, using
the full-subcategory description of line bundles.

## Identity and composition

`comparisonTwistIso_refl` identifies the comparison for equal atlases with
equality transport along `comparisonIso_refl`, followed by the canonical
identity-pullback isomorphism. The proof applies the published
`compIso_id_left_congr` to the actual maps and their factorization equality.

`comparisonTwistIso_comp` proves

`f_ab^*((b.comparisonTwistIso hM c).hom) ≫ (a.comparisonTwistIso hM b).hom`

`= compHom f_ab f_bc f_ac (a.comparisonIso_hom_comp hM b c) (t_c^* N)`

`  ≫ (a.comparisonTwistIso hM c).hom`,

The Lean formula writes out each defining
`compIso` expression and its module argument. Its proof specializes
`LineBundleFlatDescent.compIso_assoc` in the reverse direction and replaces
`compIso` homs by `compHom`. All factorization equalities come from the
constructed scheme comparisons.

## Standard charts and actual common-open coordinates

For every `U : a.opens`, `twistChartIso hM U` identifies the chart pullback
of `a.twistOne hM` with the standard
`(RelativeProjectiveSpace.twistOne U.val.toScheme n).obj`. It composes the
canonical comparison for the chart square, the pullback of
`FrameBundle.twistOneModuleIso`, and the degree-one isomorphism for the
global linear action of `a.comparisonCoordinate U`.

For an open `U : S.Opens` belonging to both bases, `changeCoordinate b U ha hb`
is obtained from the change between the two genuine dual frames on `U`,
transporting its coefficients to global sections of `U.toScheme`.
`changeCoordinate_comparison` proves that this change followed by the
second atlas's change to the fixed frame equals the first atlas's change
to the fixed frame. This uses `LocalFrame.change_trans` and
`ProjectiveSpace.coordinateBaseChange_trans`.

`chart_comparisonIso_hom` consequently proves the actual scheme-chart formula

`a.cocycle.chart ⟨U, ha⟩ ≫ f_ab`

`= globalLinearAction n (a.changeCoordinate b U ha hb)`

`  ≫ b.cocycle.chart ⟨U, hb⟩`.

The proof cancels `t_b`, applies the existing chart formulas into the fixed
frame bundle, and uses composition of global linear actions together with
the coordinate identity just proved.

## Scope

The construction needs only the specified local-freeness hypothesis, genuine
frame atlases, and, for the last formula, membership of one open in both bases.
The line-bundle chart compatibility equation on that common open remains a
further obligation. This unit also leaves tensor-line invariance, relative
cubic embeddings, the Hilbert quotient, and
`LargeLevelRepresentabilityStatement` unproved.
