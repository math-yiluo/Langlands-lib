import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Global.AdelicIwasawaStatement

/-! # Smoothness of the Iwasawa height in the infinite variable

For a connected reductive group `G` over a number field, a parabolic `p : P → G` and a maximal
compact subgroup `K` of `G(𝔸)` with `P(𝔸) K = G(𝔸)`, the Iwasawa height `H_P` of
`IsIwasawaCompact.height` pairs smoothly with every complex character parameter in the infinite
variable: `a ↦ ⟨λ, H_P(a, b)⟩` is smooth on the infinite adelic points for every finite adelic
point `b`. Equivalently `g ↦ m_P(g)^λ` has smooth infinite slices. -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- Smoothness of the Iwasawa height pairings (Bernstein–Lapid §2.2; Mœglin–Waldspurger I.1.4).
For a connected reductive group `G` over a number field `F`, a parabolic subgroup `p : P → G` and
a maximal compact subgroup `K` of `G(𝔸)` with `P(𝔸) K = G(𝔸)`, the Iwasawa height pairs smoothly
with every complex character parameter: for every `λ` and every finite adelic point `b`, the
function `a ↦ ⟨λ, H_P(a, b)⟩` on the infinite adelic points is smooth for the Lie group structure
given by `hsmooth`. -/
def IwasawaSmoothHeightPairingsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (p : P ⟶ G) (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    IsConnectedReductive G → IsParabolicSubgroup p → IsMaximalCompactSubgroup F G K →
      hK.HasSmoothHeightPairings hsmooth

end Langlands.Global
