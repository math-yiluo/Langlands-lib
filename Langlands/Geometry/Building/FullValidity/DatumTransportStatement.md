# Full corrected KP datum transport under based group isomorphisms

`Langlands.Geometry.Building.KPBuildingDatumTransportStatement`, in module
`Langlands.Geometry.Building.FullValidity.DatumTransportStatement`, is a
Prop-valued definition of the general one-group transport target. This module
states the target; it supplies no construction or proof.

For every universe `u`, it quantifies over every nonarchimedean local field
`F : Type u`, with `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, every two group schemes `G, H` over
`Spec (CommRingCat.of F)` with affine structure morphisms, and every supplied
`D : KPBuildingDatum G` satisfying `D.SatisfiesGroupAxioms`.
Connected reductivity of `G` is already a field of `D.base`; the ambient
isomorphism transports it to `H`. No additional splitness, tameness, rank or
residue-characteristic restriction is imposed.

For every commutative group scheme `S` over `Spec F`, morphism
`i : S.toGrp ⟶ H`, ambient isomorphism `f : G ≅ H` and torus isomorphism
`σ : D.base.S ≅ S` satisfying

```lean
D.base.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ i
```

the target asks for `D' : KPBuildingDatum H` with all of the following:

- `D'.SatisfiesGroupAxioms`;
- the exact equality `D'.base.S = S` and the heterogeneous equality
  `HEq D'.base.i i`;
- an equivalence `Φ : D.base.ReducedBuilding ≃ D'.base.ReducedBuilding`
  satisfying `ValuationBuildingData.IsEquivariantBuildingIso` along
  `rationalPoints.map f.hom`;
- `ValuationBuildingData.IsBuildingIso` for `Φ.symm` from the target data to
  the source data.

Although `S` is quantified as a commutative group scheme, its isomorphism
with `D.base.S` makes it a torus. The commuting square identifies `i` with
the transported maximal split torus inclusion. Heterogeneous equality is
needed because the domains of `D'.base.i` and `i` depend on their torus
objects. Together the two equality clauses prescribe the requested embedded
torus.

`IsEquivariantBuildingIso` includes preservation and reflection of facets
and apartments and an affine chart comparison on every source apartment.
Its equivariance clause is precisely
`Φ (g • y) = rationalPoints.map f.hom g • Φ y`. The final clause requires
affine chart comparisons in the reverse direction for the same `Φ`.
The current `IsBuildingIso.exists_affineEquiv` is oriented, so this reverse
clause is stated explicitly.

The validity hypothesis and conclusion use all nine fields of
`KPBuildingDatum.SatisfiesGroupAxioms`:

| Field | Corrected KP axiom |
| --- | --- |
| `building` | One-group part of 4.1.1 |
| `boundedSubgroups` | 4.1.2 |
| `affineStructure` | 4.1.4 |
| `affineRootSystem` | 4.1.6 |
| `rootGroupAction` | 4.1.8 |
| `titsSystem` | 4.1.9 |
| `iwahoriDecomposition` | 4.1.16 |
| `bruhatTitsGroupSchemes` | 4.1.20 |
| `reductiveQuotients` | 4.1.22 |

Thus the target concerns a full supplied datum: parahoric zero data,
polysimplicial realization, apartment splitting, the integral model family
with its morphisms and integral split tori, the special-fibre radical and
quotient family, and relative root reflection data. The future proof must
supply all these fields coherently on the target and establish their
axioms. In particular, transport of the valuation building alone does not
provide the model and quotient witnesses.

The proposition requires existence of such target data and the displayed
building comparison. It does not identify each target field with a named
transport construction, or impose functoriality or uniqueness. It has no
premise asserting a valid assignment, existence of one, or any other
unproved named target. The cross-group comparison clauses of Axiom 4.1.1
and the assignment-level Axiom 4.1.17 are outside
`SatisfiesGroupAxioms`. This local target supplies a prerequisite for
assignment rebasing; it does not itself assert assignment rebasing.

## Source correspondence and derived provenance

The source for the supplied data and axioms is Tasho Kaletha and Gopal
Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Definition 4.1.26 is at printed p.165 / PDF p.196. The relevant individual
axioms are at printed pp.157–164 / PDF pp.188–195: 4.1.1 on the building
and its comparisons; 4.1.2 on bounded open stabilizers; 4.1.4 on affine
structure; 4.1.6 on affine roots; 4.1.8 on root-group actions; 4.1.9 on the
Tits system; 4.1.16 on Iwahori decomposition; and 4.1.20–4.1.22 on integral
models and special-fibre quotients. Axiom 4.1.17, printed p.162 / PDF
p.193, motivates the equivariance convention for ambient isomorphisms.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.27, replace the definition's list by all ten axioms 4.1.1, 4.1.2,
4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. The same
page corrects AS 3, emphasizes nonempty bounded subsets in 4.1.8(2), and
corrects 4.1.9. This statement uses the existing corrected predicates of
`FullValidity.Assignment` without changing them. Axiom 4.1.27 is not in
the corrected definition.

The new proposition is an internal derived transport target for those
published interfaces. The literature is not claimed to state this
implementation-specific proposition separately. Its field scope is the
Library's nonarchimedean local fields of either characteristic.

The expected construction begins with `KPApartmentData.transport` for
the simultaneous torus and ambient isomorphisms. Existing
`CrossTorusReducedBuilding` supplies quotient transport in that setting.
`ValuationBuildingIsoTransport` instead treats an ambient isomorphism
while retaining the source torus; `ValuationBuildingIsoGeometry` supplies
geometric comparisons for that construction.
`ValuationBuildingRealizationTransport` transfers realizations under
supplied geometric comparisons. These interfaces motivate the target,
but do not establish transport of the complete model and quotient
families or all the group axioms. That proof remains a separate obligation.
