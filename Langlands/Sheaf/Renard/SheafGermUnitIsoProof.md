# Renard II.2.1: the canonical germ unit is invertible on sheaves

Worker 1215 implemented this proof. Worker 6 contributed the original-source
audit, focused specification and proof design. The entry theorem is
`Langlands.Sheaf.Renard.renardSheafGermUnitIso :
RenardSheafGermUnitIsoStatement.{u,v}`. It proves the entire unchanged
published aggregate, including all five conjuncts.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.2.1, first
remark on printed p.37 / PDF p.43. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.41–43 were read directly for this proof. The remark identifies an
actual sheaf with its locally represented original germ families by the
canonical map itself. The preceding page constructs that map and descent
into a target sheaf. The supplementary 2010-edition *Corrections et
compléments*, registered as `renard-2010-corrections-complements`,
PDF pp.2–3, was also read; it does not replace the governing 2026 edition.

The proof imports the published `SheafGermUnitIsoStatements` and its
unchanged dependencies. It specializes the published corrected descent
to identity. No additional universal-property or adjunction premise is
used. The [source audit](../../../notes/renard/basis-sheafification-source.md)
explains the false arbitrary-presheaf separation inference in (II.2.1.3).
The imported descent compares images on every smaller basis open and
separates them only in the target sheaf. Here the target and source of
identity are the same actual sheaf.

The implemented component argument is as follows. For a basis sheaf `G`,
a basis open `U`, and a locally represented family `s`, the published
`rawGermDesc_germ` says that the germs of `rawGermDesc (𝟙 G.obj.obj) U s`
are the images of `s` under the identity stalk map. `rawStalkMap_id`
therefore gives equality with `s` at every point. Extensionality of
`GermSections` yields `sectionGerms_rawGermDesc_id`. In the other order,
`rawGermDesc_sectionGerms` recovers every original section. Applying
descent to an equality of canonical families proves injectivity;
descending any family supplies its original preimage and proves
surjectivity. This establishes `sheafSectionGermsBijective` directly on
the original section groups in universe `v`.

`sheafGermLiftUnitIso G` bundles the actual
`germSheafLiftUnit.app G.obj` as a sheaf morphism. Its inverse is literally
`liftedGermDesc (𝟙 G.obj)`. The forward-then-inverse equation is the
published `liftedGermDesc_factorization` at identity. The reverse equation
is the component argument above: the actual unit lowers `ULift.up` before
taking the original germs. `sheafGermLiftUnitNatIso` assembles these
component isomorphisms using the published unit's naturality.
`NatIso.ofComponents` supplies inverse naturality from these inverse
laws and forward naturality. Forgetting each component isomorphism proves
invertibility of the actual presheaf unit. The displayed forward and
inverse component equations are proved by reflexivity.

At original value universe `max u v`, `sheafGermUnitIso G` repeats this
construction with the actual direct canonical unit and
`germDesc (𝟙 G.obj)` as its inverse. Its first inverse equation is
`germDesc_factorization`; its second is the same original-family
calculation. `sheafGermUnitNatIso` uses direct unit naturality and starts
at the identity functor. Its two required map identifications are again
literal reflexive equalities. Forgetting a component proves the direct
unit's `IsIso` assertion.

Original-section bijectivity and the direct identification express the
source claim. The lifted construction is the internal universe packaging
of that claim: for independent `X : Type u` and original section universe
`v`, its source is the actual `sheafLiftJoint.{u,v}`, whose section groups
are `ULift` of the original groups. The germ-family universe is `max u v`.
The direct source is identity only on `BasisSheaf.{u,max u v} B`.
No functor lowering arbitrary larger-valued objects is introduced.

The argument includes every supplied topology, chosen open basis and
actual basis sheaf. No intersection closure, Hausdorffness, local
compactness, countability or nonemptiness is assumed. Pointwise
extensionality includes empty domains, and the imported descent and its
factorization include empty-cover gluing and normalized empty sections.
Thus empty spaces and empty basis opens remain covered.

The following source paragraph's equivalence with all-open sheaves,
original compact-section comparisons and scalar-module extensions remain
separate obligations. This proof establishes the stated canonical
identification and does not claim completion of II.2.1 or of the book.
