import Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
import Langlands.Representation.Smooth.FixedVectors.Definitions

/-! # Fixed vectors of smooth parts: proposition target -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The equivalence has the expected forward/inverse values and is natural. -/
def SmoothPartFixedVectorsStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ (ρ : Representation R G V) (K : OpenSubgroup G)
      (v : fixedVectors (smoothPart ρ) K.toSubgroup),
      (smoothPartFixedVectorsEquiv ρ K v : V) = v.val.val) ∧
    (∀ (ρ : Representation R G V) (K : OpenSubgroup G)
      (v : fixedVectors ρ K.toSubgroup),
      ((smoothPartFixedVectorsEquiv ρ K).symm v).val.val = v.val) ∧
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ) (K : OpenSubgroup G),
      (smoothPartFixedVectorsEquiv σ K).toLinearMap.comp
          (fixedVectorsMap (smoothMap f) K.toSubgroup) =
        (fixedVectorsMap f K.toSubgroup).comp
          (smoothPartFixedVectorsEquiv ρ K).toLinearMap)

end Langlands
