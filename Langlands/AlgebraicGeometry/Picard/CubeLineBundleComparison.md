# Three-pullback comparison using actual line-bundle inverses

This internal categorical construction turns three ordinary pullback comparisons
into an actual carrier isomorphism, provided those three maps detect ordinary
line-bundle triviality and canonical pullback-tensor comparison is invertible.
It then gives the corresponding two-restriction equality criterion for actual
relative rigidified classes. It applies to arbitrary schemes in every universe.
The ordinary triviality principle remains an explicit hypothesis.

`LineBundle.carrierIsoOfThreePullbackComparisons` uses the already published
`LineBundle.exists_tensorObj_iso_structureSheaf` to choose an actual line bundle
`N` inverse to `M`. Its evaluation is an isomorphism for the explicit sheafified
tensor. `LineBundle.tensor` constructs the actual line bundle `L tensor N`.
For each of the three maps, the published
`pullbackTensorInverseTrivialization` combines the given comparison between
pullbacks of `L` and `M` with the evaluation to trivialize the pullback of
`L tensor N`. Applying the stated ordinary triviality principle gives its global
trivialization. The comparison `localizedTensorIso` transports the evaluation
and this trivialization to the published symmetric monoidal tensor. Unit,
symmetry, and associativity isomorphisms then give
`L ≅ L tensor (N tensor M) ≅ (L tensor N) tensor M ≅ M`.
This proof does not require the general equivalence between tensor invertibility
and local freeness of rank one. The dual-evaluation theorem supplies the inverse,
and actual line-bundle tensor closure supplies the difference line bundle.

`RigidifiedLineBundle.classes_eq_of_threePullbackTrivialityWithDual` specializes
this carrier construction to the relative section and two arbitrary relative
restriction maps. Quotient induction chooses actual rigidified representatives
`L` and `M`. Each equality of restriction classes supplies a compatible
isomorphism by `Quotient.exact`; its underlying carrier isomorphism is the
corresponding ordinary pullback comparison. The two specified rigidifications
give the comparison along the relative section. The carrier construction then
gives an ordinary isomorphism, which `isoOfCarrierIso` corrects using the relative
projection, a retraction of the section. `Quotient.sound` gives equality in the
original quotient of actual rigidified line bundles. This includes full schemes
and does not pass to geometric points or reduced parameter schemes.

The implementation is internally derived from the published
`CubeIsomorphismAssembly`, `LineBundleDualEvaluation`, `LineBundleTensor`, and
`RigidifiedCarrierIso` interfaces. Its direct inverse proof follows the existing
three-pullback assembly while replacing its local-rank-one/tensor-invertibility
comparison hypothesis by the published actual inverse and tensor closure.
No source-level geometric cube theorem is asserted. Neither this construction
nor its ordinary triviality hypothesis proves unconditional relative cube
triviality or the relative Mumford parameter-additivity target. Author: Worker 579.
