# Symmetry of rigidified line-bundle tensor

This module lifts the explicit sheaf tensor swap to rigidified line bundles
and proves commutativity on relative rigidified classes and their geometric
Picard-zero subsets. Schemes use universe `u`.

The rigidified constructions assume explicitly:

- `preservation : pullbackTensorComparisonIsIsoStatement`, invertibility of
  the fixed canonical pullback tensor comparison for every scheme morphism;
- `symmetry : PullbackTensorSymmetryStatement`, the published equation that
  this same comparison commutes with the explicit tensor swap.

These are the propositions in `Langlands.Scheme.Modules`, not arbitrary
isomorphism data or assumed rigidified commutativity conclusions. The module
does not prove these global propositions. Unit coherence is not an additional
hypothesis of its commutativity results.

## The explicit sheaf tensor swap

`tensorComm_naturality` proves

`tensorMap f g ≫ tensorComm(M',N').hom = tensorComm(M,N).hom ≫ tensorMap g f`.

The actual sheaf tensor is sheafification of the sectionwise presheaf tensor,
and its explicit swap is the sheafification of the presheaf braiding. The proof
combines functoriality of sheafification with braiding naturality in the
symmetric category of presheaves of modules.

`tensorComm_structureSheaf` proves that swapping the two copies of the
structure sheaf is the identity on their tensor. In the presheaf category,
the braiding on the tensor unit is the left unitor followed by the inverse
right unitor. Those unitors agree on the unit, so the composite is identity.
Mapping this equality under sheafification gives the claimed sheaf identity.
Both of these lemmas are unconditional.

## Compatibility with rigidifications

`RigidifiedLineBundle.tensorComm_compatibility` states that pulling back the
actual sheaf swap along the rigidification morphism carries the rigidification
of `L ⊗ M` to that of `M ⊗ L`.

The proof postcomposes with the invertible canonical tensor comparison for the
target pair. The `symmetry` equation moves the pulled-back swap past that
comparison. The existing formula `tensorObj_rigidification_comp` then expands
each side to the inverse unit identification followed by the tensor of the
original rigidifications. Naturality of the sheaf swap changes the order of
those two rigidifications; its identity on the tensor of structure sheaves
finishes the equality. Thus the proof checks compatibility for the exact
rigidifications already constructed in `RigidificationTensor`.

`RigidifiedLineBundle.tensorComm` packages the actual sheaf swap and this
compatibility proof as an isomorphism of rigidified line bundles. The objects
retain their locally free rank-one properties. The rigidification morphism
may be arbitrary; no section equation or geometric restriction is needed for
this isomorphism.

## Commutativity on classes

For a relative family specified by `f : X → S`, a section `ε : S → X` and
its section equation, `RigidifiedLineBundle.classesTensor_comm` proves
commutativity on each test scheme's compatible-isomorphism classes. Quotient
induction on two classes reduces the equation to the compatible swap, and
quotient soundness gives their equality.

For an abelian scheme `A/S`, `AbelianScheme.picardZeroClassesTensor_comm`
proves commutativity of the restricted operation on `PicardZeroClasses A T`.
Subtype extensionality reduces it to the preceding equation on all rigidified
classes. Closure of the operation in that subtype is supplied by
`RelativePicardZeroTensor`.

## Provenance and scope

The construction is derived from the rigidified tensor formula and compatible
isomorphism classes of Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, paragraph (6.2), printed p.88 (PDF p.92), literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The Picard-zero subset uses the geometric translation-invariance convention
motivated by the point formula on printed p.95 (PDF p.99) and Corollary
(7.22), printed p.106 (PDF p.110), as explained in the imported modules.
The implementation is the explicit categorical calculation above, followed
by quotient soundness and subtype extensionality. It does not assert the
source's kernel comparison theorem.

These are objectwise commutativity equations. Associativity, inverses,
compatibility with relative pullback, and the complete group-valued Picard
functors remain separate obligations. The explicit canonical-comparison
premises are retained in every rigidified and quotient conclusion here.
