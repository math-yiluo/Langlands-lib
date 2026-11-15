import Langlands.BruhatTits.IntegralModels.RootDepthKernelStatement
import Langlands.BruhatTits.IntegralModels.RootDepthKernelMultipliable
import Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceProof

/-! # KP Lemma C.5.3 for actual unramified root-depth special-fibre kernels -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Lemma C.5.3, invariant under the supplied root-model presentations.**
For every nonarchimedean local field `F`, affine group scheme `G` over the maximal unramified
field with building data, apartment point, relative root `a` (multipliable or not, including
divisible roots) and depths `r ≤ s` (including `r = s`), every integral-model map between
supplied presentations of `U_{a,x,s}` and `U_{a,x,r}` whose generic map commutes with the
inclusions has a smooth, connected and unipotent special-fibre kernel.

Proof: the published conditional theorem `unramifiedRootDepthKernel_of_multipliableCoordinates`
applied to the published existence theorem `multipliableRootGroupCoordinatesExistence`. -/
theorem unramifiedRootDepthKernel : UnramifiedRootDepthKernelStatement.{u} :=
  unramifiedRootDepthKernel_of_multipliableCoordinates
    Langlands.Geometry.Building.multipliableRootGroupCoordinatesExistence

end Langlands.BruhatTits.IntegralModels
