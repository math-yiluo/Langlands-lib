# Openness of fibre components meeting a section

`Langlands.AlgebraicGeometry.SectionComponent.flatFinitePresentationOpenness`
proves the published proposition
`SectionComponent.FlatFinitePresentationOpennessStatement.{u}` in every universe
`u`. For arbitrary schemes `X` and `Y`, an actual morphism `f : X ⟶ Y`, and
an actual section `e : Y ⟶ X` with `e ≫ f = 𝟙 Y`, it assumes flatness,
local finite presentation, quasi-compactness, quasi-separatedness, and geometric
reducedness of `f`. It concludes that `componentSet f e he` is open in `X`.
This is the unchanged union of the connected components of the actual residue
fibres that contain their section points. The final theorem adds no premise
on the base or on constructibility, generic constancy, or generizations.

The implemented proof first derives Noetherian generic constancy of geometric
connectedness. `noetherianGeometricallyConnectedFiberGenericConstancy_of_fieldSplitting`
combines finite separable splitting of the actual field-scheme components with
the constructed prescribed generic cover, geometric irreducibility spreading,
and the finite closed-cover geometric-connectedness criterion. The theorem
`noetherianComponentConstructibility_of_fieldSplitting` then applies the
section-component constructibility theorem. That theorem uses the actual
selected generic component closure and induction on closed subsets of the
Noetherian base; it does not assume constructibility as an input. In the
unconditional application, `finiteSeparableComponentSplitting` supplies the
field-splitting premise.

The next step establishes `noetherianFiberwiseOpenness`, which concerns a flat,
locally finitely presented, quasi-compact and quasi-separated family over the
spectrum of a Noetherian ring. Its indexed hypothesis only requires geometric
reducedness of the residue fibre at the image of the point under consideration.
The total space is Noetherian: local finite type gives local Noetherianity, and
quasi-compactness over the compact affine base gives compactness. The constructed
component union is therefore a constructible subset of a Noetherian sober space.
For a point of that union with geometrically reduced indexed fibre,
`mem_componentSet_of_specializes_of_geometricallyReduced_fiber` shows that all
its generizations remain in the same union. The latter theorem realizes a
strict specialization by an actual DVR-valued point and applies the two-section
DVR connectedness argument. The topological theorem
`mem_interior_of_isConstructible_of_generizations` turns this generization
membership into interior membership. The conditional helper in this file
records these two inputs explicitly; `noetherianFiberwiseOpenness` supplies both
proved inputs.

Finally, `flatFinitePresentationOpenness_of_noetherianFiberwise` reduces the
arbitrary base to affine opens and descends each affine family with its section
to an actual Noetherian model. The component union commutes with the Cartesian
comparison. At each original point, geometric reducedness of its actual residue
fibre descends to the corresponding model fibre. The Noetherian interior result
supplies a neighbourhood in the model component union, and continuity pulls
this neighbourhood back. This proves openness in the original total space.
The argument uses reducedness only at the indexed model fibre; it does not need
geometric reducedness of the entire model family at a finite stage.

The source target is EGA IV, Troisième partie (1966), Corollary 15.6.5, printed
pp.238–239 (one-based retained PDF pages237–238). Its preceding Proposition
15.6.4, printed pp.237–238, motivates the generization and DVR step; Proposition
9.7.12, printed p.83, supplies the constructibility context. The registered
source is `ega-iv3-grothendieck-dieudonne-1966`, SHA-256
`f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`.
The proof above is the implemented internal assembly of those stages and the
Library's actual-fibre comparisons. The original EGA IV, Quatrième partie,
List III §15 errata were checked in the statement's source audit; no correction
to Corollary 15.6.5 is listed there.

All five morphism hypotheses and the arbitrary common universe are retained.
This proves the stated finite-presentation openness result. Applications to
smooth group schemes still require their local finite-presentation reduction
and group arguments; relative group-component structure, normality, and further
base-change assertions are separate obligations.
