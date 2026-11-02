# Zariski separation of general relative rigidified classes

This internal generalization of the published rigidified Zariski separation
proof uses arbitrary schemes `S`, `X`, a map `f`, a section `ε` and its
section law. Its explicit input is uniqueness of isomorphisms between all
relative rigidified line bundles. The final helper
`classes_zariskiSeparated_of_unique` says that two existing global rigidified
classes agreeing on an arbitrary Zariski open cover of the test scheme are
equal. The uniqueness input is not proved in this module.

`relativeSpace_openCover_map` and `relativeOpenCover` identify the actual
base change of an open cover with a cover of the relative total space.
`rigidified_common_map` compares local isomorphisms after pullback to a
common slice object; uniqueness identifies these comparisons.
`rigidified_overlap_compatible` transports this equality through the actual
pullback-preservation isomorphism and obtains the module overlap equation.
`rigidified_iso_of_local_isos` glues the module isomorphisms with the published
module-map gluing theorem and checks the rigidification on the base cover.
Quotient induction and soundness give the final equality of classes.

The construction follows and imports the generic helpers of the published
`RigidifiedClassesZariskiSeparatedProof` and
`RigidifiedClassesZariskiGluingProof`; their abelian-scheme hypotheses are
replaced here by the precise uniqueness input used on overlaps. This is a
derived internal helper for the general comparison in EVM Chapter VI §1,
(6.2), and makes no new assertion about that source. No affineness,
reducedness, finiteness, properness or representability is assumed. It does
not assert effective gluing of local classes or the fppf sheaf condition.
