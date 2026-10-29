import Langlands.Representation.Exponents.Jacquet

/-! # Open kernels of generalized characters of smooth actions -/

namespace Langlands

universe uR uG uV

/-- Every uniform generalized eigencharacter of a smooth representation over
a field has open kernel. No topology on the field or carrier is required. -/
def SmoothGeneralizedEigencharacterOpenKernelStatement : Prop :=
  ∀ (k : Type uR) [Field k]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module k V]
    (π : Representation k G V) (χ : G →* kˣ),
    IsSmooth π → IsGeneralizedEigencharacter π χ →
      IsOpen (χ.ker : Set G)

end Langlands
