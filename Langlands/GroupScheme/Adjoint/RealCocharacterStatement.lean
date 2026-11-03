import Langlands.GroupScheme.Adjoint.SplitTorus
import Langlands.Geometry.Building.KPApartment

/-! # The actual adjoint real cocharacter and root-annihilator comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- For an actual adjoint quotient `q : G ⟶ A` of a connected reductive group
over any field, and the actual image `p : T ⟶ T_ad` of a maximal split torus
`i : T ⟶ G` in a maximal split torus `j : T_ad ⟶ A`, real postcomposition of
cocharacters along `p` is surjective with kernel the common annihilator of the
actual relative roots. Hence the apartment translation space `V(T)` modulo
that annihilator is identified with `V(T_ad)` by the map induced by `p`. -/
def AdjointRealCocharacterComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G A : GroupScheme (Spec (CommRingCat.of k)))
    (T T_ad : CommGroupScheme (Spec (CommRingCat.of k)))
    (q : G ⟶ A) (i : T.toGrp ⟶ G) (j : T_ad.toGrp ⟶ A) (p : T ⟶ T_ad)
    (h : IsAdjointSplitTorusImage q i j p),
    haveI := h.isAdjointQuotient.isConnectedReductive.isAffineHom
    Function.Surjective (cocharacterMapReal p) ∧
    LinearMap.ker (cocharacterMapReal p) = relativeCentralDirections i ∧
    ∃ e : Langlands.Geometry.Building.TranslationSpace i ≃ₗ[ℝ] V T_ad,
      ∀ v : V T, e (Submodule.Quotient.mk v) = cocharacterMapReal p v

end Langlands.GroupScheme
