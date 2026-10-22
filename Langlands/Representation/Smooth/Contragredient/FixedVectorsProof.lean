import Langlands.Representation.Smooth.Contragredient.FixedVectorsStatement

/-! # Evaluation, factorization and naturality for fixed smooth functionals -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem smoothDualFixedEquiv_apply (ρ : Representation R G V) (K : OpenSubgroup G)
    (ℓ : fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K.toSubgroup) (v : V) :
    (smoothDualFixedEquiv ρ K ℓ).val v = smoothDualPairing ρ ℓ.val v := rfl

theorem smoothDualFixedRestriction_apply (ρ : Representation R G V) (K : Subgroup G)
    (ℓ : fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K) (v : fixedVectors ρ K) :
    smoothDualFixedRestriction ρ K ℓ v = smoothDualPairing ρ ℓ.val v.val := rfl

theorem smoothDualFixedRestriction_factor (ρ : Representation R G V) (K : OpenSubgroup G) :
    smoothDualFixedRestriction ρ K.toSubgroup =
      (fixedVectors ρ K.toSubgroup).subtype.dualMap.comp
        ((fixedVectors ρ.dual K.toSubgroup).subtype.comp
          (smoothDualFixedEquiv ρ K).toLinearMap) := by
  ext ℓ v
  rfl

theorem smoothDualFixedRestriction_natural {ρ : Representation R G V}
    {σ : Representation R G W} (f : ρ.IntertwiningMap σ) (K : Subgroup G) :
    (smoothDualFixedRestriction ρ K).comp
        (fixedVectorsMap (contragredientMap f) K) =
      (fixedVectorsMap f K).dualMap.comp (smoothDualFixedRestriction σ K) := by
  ext ℓ v
  rfl

omit [IsTopologicalGroup G] in
theorem smoothDualFixedVectors :
    SmoothDualFixedVectorsStatement (R := R) (G := G) (V := V) (W := W) := by
  intro _
  exact ⟨smoothDualFixedEquiv_apply, smoothDualFixedRestriction_apply,
    smoothDualFixedRestriction_factor, fun _ _ f K => smoothDualFixedRestriction_natural f K⟩

end Langlands
