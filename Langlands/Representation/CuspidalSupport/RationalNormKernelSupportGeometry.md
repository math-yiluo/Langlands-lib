# Uniform norm-kernel support from one joint special-compact geometry

This internal assembly proves the exact uniform-support target
`Langlands.CuspidalSupport.RationalNormKernelUniformSupportStatement.{uF, uV}`
under one explicit hypothesis: the published existence statement
`JointSpecialCompactBasisExistenceStatement.{uF}` for joint special-compact
witnesses. It does not prove that hypothesis, so it does not prove the
uniform-support target unconditionally. The target statement and its imports
are unchanged.

`NormKernelUniformSupportGeometry i ν` collects the geometric input of the
support argument, for a finite simple-root type. Its fields are:

- a family of corrected fundamental cocharacters, `NormKernelFundamentalCocharacters i ν`;
- one subgroup `K0` of the ambient rational points, compact in the point topology;
- a simultaneous standard basis `SimultaneousStandardBasisAt i ν K0`;
- a finite central Cartan cover `NormKernelCentralCartanCover` for exactly that
  generator family and that `K0`.

The same compact subgroup appears in the basis and in the cover.

`NormKernelUniformSupportGeometry.nonempty_of_joint` builds such a package from
the joint hypothesis, connected reductive `G`, a maximal split torus, a generic
cocharacter, the standard-cocharacter statement and a relative root system.
The generators come from the existing `nonempty_normKernelFundamentalCocharacters`.
The joint witness gives an apartment datum `D` and a special vertex `x`. It also
gives the centralizer inclusion `j`, the torus map `s` with `s ≫ j = i`, and the
bijective restriction evaluation. It supplies the special compact properties as
well, and from them we take compactness of `D.specialCompactSubgroup x`. Finally
it supplies the standard-Levi compatibility and the simultaneous standard basis
at that subgroup. The published `exists_isFiniteLatticeTransversal` gives a
finite lattice transversal from the compatibility. Then
`exists_finite_centralCartanFactorization` gives a finite residual set and a
factorization of every ambient point as `k₁ * (orthant * t) * k₂ * z`, where
both compact factors lie in `D.specialCompactSubgroup x` and `z` is central.
The proof only reorders these witnesses into the cover record. The other
clauses of the joint witness are not used.

`NormKernelUniformSupportGeometry.hasUniformSupport` assumes the ambient rational
points are locally compact, nonarchimedean and Hausdorff. Under these
assumptions it proves `HasUniformFixedLevelCoefficientSupport.{uF, uV}` at every
open subgroup `U` of the actual common norm kernel. It obtains a common
compression level below `U` from the existing `nonempty_normKernelCompressionLevel`,
using the package's generators, compact subgroup and basis. It then equips the
kernel with its Borel σ-algebra and the canonical Haar measure `Measure.haar`. The
kernel is locally compact because it is open in the ambient group. The proof
finishes with the existing `hasUniformSupport_of_centralCartanCover` and the
package's compactness and cover. That theorem already moves support from the
common level to `U`. The choice of Borel measurable structure and Haar measure is
internal to this proof; the conclusion does not mention any measure.

`Langlands.CuspidalSupport.rationalNormKernelUniformSupport_of_joint` is the
implication from `JointSpecialCompactBasisExistenceStatement.{uF}` to
`RationalNormKernelUniformSupportStatement.{uF, uV}`. The carrier universe `uV`
is independent of the field universe `uF`. Finiteness of the simple roots comes
from the existing `finite_simpleRoot`, and a `Fintype` instance is chosen from
it. The target's closed-unipotent hypothesis is not used, and neither is
compactness of the prescribed open subgroup. The field may have any
characteristic, and an empty simple-root type is allowed.

Provenance: internal assembly of existing Library results and approved
collaborative adapters. These are the corrected fundamental cocharacters, the
common compression level, the support sandwich from central Cartan charts, and
Worker 1610's ambient central Cartan cover. This assembly is the
class-uniform coefficient-support step used in Renard VI.3.4. The existence of a
joint special-compact witness is a separate prerequisite that this file leaves
open.
