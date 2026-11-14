# Actual torus/root comparison kernels

This internal supporting unit combines supplied torus/root model families
`A` and `B` over the maximal unramified integers, their actual comparison
maps and the ordered product-chart kernel comparison. The families share
`F`, `G`, `C`, `E` and `x`, with subsets `Ω` and `Ω'` and ambient models
`N` and `N'`. The homomorphism-extension criterion and all root-depth
inequalities remain explicit inputs.

`comparisonKernel` is the actual scheme-theoretic kernel of each comparison
map after base change to the actual residue field. Every such kernel is
affine, by its closed inclusion in its affine source special fibre. This
uses affineness of the target special fibre to obtain separatedness.

`comparisonKernel_smooth_affine_connected` additionally takes the explicit
premise `UnramifiedRootDepthKernelStatement`. At the torus index, the
comparison is an actual special-fibre isomorphism; its kernel is isomorphic
to the residue-field spectrum, hence smooth, affine and connected. At a
root index, the premise applies to the actual root models, their canonical
generic isomorphism and the actual extended comparison. It supplies
smoothness and connectedness, while affineness is already established.
No proof of the root-depth premise is claimed here.

For any function `e : Fin n → Option (relativeRoots C.i)`,
`orderedComparisonKernelIso` applies the published ordered-multiplication
kernel comparison to the model maps selected by `e`. The inputs include
monomorphy of both integral ordered charts and a morphism lifting the
entire special-fibre kernel into the residue pullback of the source
chart's product. The lift's composite with the chart must be exactly the
kernel inclusion. The conclusion is an isomorphism over the residue field
from the product of the actual comparison kernels to the actual ambient
kernel. It is a scheme isomorphism; no compatibility with the direct-product
group law is asserted.

`smooth_connected_kernel_of_orderedCharts` uses the same data, together
with the explicit root-depth premise, to prove smoothness and connectedness
of the ambient special-fibre kernel. Compatibility of the charts follows
from the already constructed ambient comparison squares. The finite
function `e` need not be an equivalence or injective: monomorphy and the
full-kernel lift are the precise hypotheses required by the generic
comparison. In particular, this API can select only indivisible roots
and the torus, in any ordering for which those hypotheses hold, and also
handles an empty list.

The provenance is internal composition of the published kernel, model,
comparison and product APIs, together with the explicitly named root-depth
premise. This unit constructs neither family, proves no open immersion
or full-kernel lift, and proves no ambient unipotence. It therefore leaves
the unconditional host theorem and the root-depth proof as separate
obligations. Affine closure ordering can supply its depth inequalities
through `rootDepth_le_of_subset_affineClosure` from the companion module.
