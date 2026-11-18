# Valuation pullbacks of groups with affine residue fibres

Worker 584. `Langlands.GroupScheme.HasAffineResidueFibers G` names the fibre
hypothesis of Task 7705. It asks for affineness over the residue field of each
actual group `RelativeIdentityComponent.residueFiber G s`. Raynaud names affine
fibres as a case of Corollary 8.11, recomposed p. 295.

For a field-valued point `Spec k → S`, its stalk map factors the point through
the spectrum of the residue field of its image. The group pullback comparison
and stability under base change transport residue-fibre affineness to this
actual field pullback. Applying the comparison twice proves that arbitrary
base change preserves affineness of every residue fibre.

A pullback to the spectrum of a DVR inherits smoothness, separatedness and
quasi-compactness. Its generic fibre is the field pullback along the composite
with the fraction-field point, so it is affine. The published
`smoothDvrGenericAffineness` then gives affineness over the DVR.

With that affine target, the published comparison for a diagonalizable source
algebraizes compatible homomorphisms over the adic quotients of a complete
DVR. This treats the valuation base in SGA 3, Exposé XV, Corollary 4.4 by using
Prasad–Yu's DVR criterion as implemented by `smoothDvrGenericAffineness`.
The smooth universal family over the DVR follows directly from the Library's
smooth affine-target result and retains its universal property on all tests.

Source for the adic application is Raynaud, SGA 3, Exposé XV, Corollary 4.4,
recomposed p. 260, registered `sga3-expose-xv-raynaud-2008`, SHA-256
`03647e0232067a7508bb1350e7aace3e88d58872956f068ced808a4f9cc3273f`.
