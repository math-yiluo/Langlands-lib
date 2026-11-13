import Langlands.GroupScheme.Reductive.TitsKernelIndexData
import Langlands.GroupScheme.Reductive.TitsIndexAnisotropicKernelProof

/-! # Proof: the index of the semisimple anisotropic kernel is the subdiagram on `Δ₀` -/

universe u

namespace Langlands.GroupScheme

/-- **Tits §§2.2–2.3.** Every actual derived subgroup of every actual
representative of the centralizer of the maximal split torus of actual Tits
index data is affine and locally of finite type, and has actual index data whose
index is the subdiagram on `Δ₀`. -/
theorem titsAnisotropicKernelIndex : TitsAnisotropicKernelIndexStatement.{u} :=
  titsAnisotropicKernelIndex_of_anisotropicKernel titsAnisotropicKernel

end Langlands.GroupScheme
