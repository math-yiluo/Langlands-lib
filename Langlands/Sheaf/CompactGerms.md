# Compact global germs on locally profinite spaces

This internal construction supports the restriction functors of Renard 2026,
III.3.2, printed p.84 / PDF p.90. It supplies the actual compact-section germ
map needed to show that the point restriction of a smooth action is smooth.
The original-section germ map also occurs in II.2.5, printed pp.40–42 /
PDF pp.46–48. The surjectivity argument here is an intrinsic construction law,
not a statement of the III.3.1 coinvariant-fibre proposition.

All names below have prefix `Langlands.Sheaf.CompactGerms`.

`additive` forgets scalars from the original module sheaf by Mathlib's
`sheafCompose`. `extend` uses the already published
`Langlands.Sheaf.ClopenExtension.extend` on that additive sheaf. Its output
retains the original module carrier. `restrict_extend` is the original
zero-extension restriction law on elements. `support_extend_subset` uses
vanishing on the complementary open and the original module-valued germ maps
to show that this extension has support contained in the clopen. Since that
support is closed, `compactExtension` bundles the extension from a compact
clopen into the published `CompactSupport.submodule`.

`germ F x` is literally the original global germ linear map composed with
the inclusion of compact global sections. `germ_surjective` assumes
`Langlands.Topology.IsLocallyProfinite X`, including Hausdorffness and the
compact-open neighborhood basis. An original stalk element has a local
section representative by Mathlib's filtered-colimit stalk construction.
Refine its neighborhood to a compact open, restrict the representative,
and apply the published additive zero extension. Its support is a closed
subset of that compact open. The restriction law and original germ
restriction law give exactly the original stalk element. No comparison
between additive and module stalks, sheaf/module equivalence, or supplied
stalk inverse is assumed.

`germ_naturality` states that actual sheaf morphisms commute with this germ
map. It is the published original stalk-map naturality formula, restricted
to compact sections. No action or smoothness hypothesis is needed for these
ordinary constructions.

The coefficient ring, base space and section carriers have the same universe
`u`, as required by the published `CompactSupport` interface. There are no
finite-dimensionality hypotheses or topology on the section modules. Taking
`R = ℂ` specializes this interface to universe zero, as in the III.3 action
sheaf constructions. The main source is David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
