import Langlands.Representation.Smooth.SmoothPart.FixedVectorsStatement

/-! # Fixed vectors of smooth parts: draft proof -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem smoothPartFixedVectorsEquiv_apply (ρ : Representation R G V)
    (K : OpenSubgroup G) (v : fixedVectors (smoothPart ρ) K.toSubgroup) :
    (smoothPartFixedVectorsEquiv ρ K v : V) = v.val.val := rfl

theorem smoothPartFixedVectorsEquiv_symm_apply (ρ : Representation R G V)
    (K : OpenSubgroup G) (v : fixedVectors ρ K.toSubgroup) :
    ((smoothPartFixedVectorsEquiv ρ K).symm v).val.val = v.val := rfl

theorem smoothPartFixedVectorsEquiv_natural {ρ : Representation R G V}
    {σ : Representation R G W} (f : ρ.IntertwiningMap σ) (K : OpenSubgroup G) :
    (smoothPartFixedVectorsEquiv σ K).toLinearMap.comp
        (fixedVectorsMap (smoothMap f) K.toSubgroup) =
      (fixedVectorsMap f K.toSubgroup).comp
        (smoothPartFixedVectorsEquiv ρ K).toLinearMap := by
  ext v
  rfl

omit [IsTopologicalGroup G] in
theorem smoothPartFixedVectors :
    SmoothPartFixedVectorsStatement (R := R) (G := G) (V := V) (W := W) := by
  intro _
  exact ⟨smoothPartFixedVectorsEquiv_apply, smoothPartFixedVectorsEquiv_symm_apply,
    fun _ _ f K => smoothPartFixedVectorsEquiv_natural f K⟩

end Langlands
