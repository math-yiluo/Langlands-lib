# Real Jacquet integrals in lower Levi and radical coordinates

`RealLeviJacquetChartStatement` gives a change of variables for an integrable
kernel on the full lower unitriangular chart. The kernel consists of a
function of the lower matrix times the additive character of a weighted
sum of its adjacent lower entries. Each simple entry may have its own real
frequency. The formula integrates first in the lower Levi entries and then
in the opposite radical entries, with Lebesgue measure on both factors.

The proof applies the measure-preserving shear of `RealLeviShear`. This
shear expresses the lower matrix as a product of the lower Levi matrix and
the opposite radical matrix. At an adjacent entry inside a block, the
product has the Levi entry. At a boundary between two blocks, the only
contributing term is the diagonal-one Levi entry times the radical entry.
`simpleLowerEntry_shear` records this partition of the phase, and Fubini
gives the iterated integral.

`additiveJacquetIntegral_eq_levi` applies the formula to the real Jacquet
integral at a positive torus translate where its upper kernel is integrable.
Conjugation by the positive torus moves the diagonal to the left of the
open-cell variable. This substitution contributes the upper-unipotent
modulus. The long Weyl element reverses both entry indices, giving the
full lower chart and reversing the diagonal. At lower slot \(i+1,i\), the
frequency multiplier is \(\exp(y_{(i+1)^{\rm rev}}-y_{i^{\rm rev}})\).
The self-dual measure for the real unit \(a\) contributes the further
factor `entryScale`, the product of \(\sqrt{|a|}\) over the lower entries.
The additive character in the lower integral has the original scale.

This formula combines the upper-entry Jacquet integral in
`RealGodementAdditiveJacquet` with `map_conjTorus`, the scalar self-dual
measure and the lower-coordinate factorization in `RealLeviShear`.
