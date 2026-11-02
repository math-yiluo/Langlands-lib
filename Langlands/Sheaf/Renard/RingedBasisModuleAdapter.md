# Renard II.2.3: constructing module sheaves on original section groups

This unit supplies the construction adapter for the module sheaves defined in
`RingedBasisModules`. Its source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.2.3 “Faisceau de
modules”, printed p.38 / PDF p.44. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original PDF pp.44–45 were read for this unit.

Renard equips the original groups of sections of a sheaf with left module
structures over the rings of sections and requires the original restrictions
to be linear after restriction of scalars. Here `F` is an existing
`BasisSheaf B`, `S` is an actual ring presheaf, and the constructor consumes
actual `Module (S.obj (op U)) (Sections F.obj.obj U)` structures at every basis
open. For the source interpretation as modules over a ring sheaf, take
`S = R.ring` for `R : RingedBasis B`; that package retains the exact intrinsic
ring-sheaf proof. The adapter also makes sense over an arbitrary ring
presheaf, without asserting that the ring presheaf is a sheaf.

`BasisSheaf.SemilinearRestrictions F S` is the literal equation
`restriction (a • m) = ringRestriction a • restriction m` for every inclusion
of basis opens, on the original sections and supplied actions.
`BasisModuleSheaf.semilinear_map` passes this proved law to all arrows of the
opposite basis category. Its proof identifies each arrow with the opposite
of the inclusion given by its underlying order relation, using the published
thinness of the basis category. It imposes no intersection-closure hypothesis.

`BasisModuleSheaf.ofBasisSheaf` uses Mathlib's actual
`PresheafOfModules.ofPresheaf` with this law, together with the original
sheaf proof. It does not construct or assume an action that has not been
supplied. `ofBasisSheaf_presheaf`, `ofBasisSheaf_sections` and
`ofBasisSheaf_restrict` expose the unchanged additive presheaf, given section
modules, and original restriction values. `ofBasisSheaf_toBasisSheaf` proves
equality with the original bundled basis sheaf after forgetting the action.
These recovery equalities are definitional; proof irrelevance identifies
the normalization proofs. As in the core construction, normalization of the
result is derived from its sheaf proof rather than added as independent data.

`BasisSheaf.PreservesModuleScalars F G S f` requires componentwise scalar
preservation for the actual additive sheaf morphism `f`. The lift
`BasisModuleSheaf.ofBasisSheafHom` consumes precisely this proof and calls
the core `homMk`, which uses Mathlib's `PresheafOfModules.homMk`.
`ofBasisSheafHom_app` gives the unchanged value on each original section,
and `ofBasisSheafHom_toBasisSheaf` recovers the given bundled sheaf morphism.
The latter proof uses extensionality of the full subcategories and of the
underlying additive natural transformation. No unrestricted additive
transformation is declared scalar-linear.

The construction adapter and categorical recovery laws are internal formal
packaging of the source definition. Their application to arbitrary supplied
topological spaces generalizes the chapter's totally disconnected setting.
The space, ring-carrier and module-carrier universes `u`, `r` and `v` remain
independent. Empty spaces, empty bases and empty basis opens are retained,
with no separation, compactness, smallness or nonemptiness hypothesis.
This unit makes no locally constant action, scalar-restriction, basis-change
or II.2.5 equivalence construction.

Worker 1203 implemented the adapter and its recovery laws. Worker 633 supplied
the imported actual module-sheaf category. Worker 6 contributed the original
source audit and the actual-section module-presheaf interface design recorded
in the task.
