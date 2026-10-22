import Langlands.Representation.MatrixCoefficient.LawsStatement

/-! # Translation, naturality, and smoothness of matrix coefficients -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

@[simp]
theorem matrixCoefficient_apply (ρ : Representation R G V)
    (ℓ : Module.Dual R V) (v : V) (g : G) :
    matrixCoefficient ρ ℓ v g = ℓ (ρ g v) := rfl

theorem matrixCoefficient_mul (ρ : Representation R G V)
    (ℓ : Module.Dual R V) (v : V) (g h : G) :
    matrixCoefficient ρ ℓ v (g * h) = matrixCoefficient ρ ℓ (ρ h v) g := by
  simp [matrixCoefficient, map_mul]

theorem matrixCoefficient_mul_left (ρ : Representation R G V)
    (ℓ : Module.Dual R V) (v : V) (g h : G) :
    matrixCoefficient ρ ℓ v (h * g) = matrixCoefficient ρ (ρ.dual h⁻¹ ℓ) v g := by
  change ℓ (ρ (h * g) v) = ℓ (ρ (h⁻¹)⁻¹ (ρ g v))
  simp [map_mul]

theorem matrixCoefficient_intertwining {ρ : Representation R G V}
    {σ : Representation R G W} (f : ρ.IntertwiningMap σ)
    (ℓ : Module.Dual R W) (v : V) :
    matrixCoefficient σ ℓ (f v) = matrixCoefficient ρ (dualIntertwining f ℓ) v := by
  funext g
  change ℓ (σ g (f v)) = ℓ (f (ρ g v))
  rw [f.isIntertwining]

theorem matrixCoefficient_biInvariant [TopologicalSpace G]
    (ρ : Representation R G V) (ℓ : Module.Dual R V) (v : V)
    (hℓ : IsSmoothVector ρ.dual ℓ) (hv : IsSmoothVector ρ v) :
    ∃ K : OpenSubgroup G, ∀ (k : K) (l : K) (g : G),
      matrixCoefficient ρ ℓ v ((k : G) * g * (l : G)) = matrixCoefficient ρ ℓ v g := by
  obtain ⟨K, hK⟩ := hℓ
  obtain ⟨L, hL⟩ := hv
  refine ⟨K ⊓ L, ?_⟩
  intro k l g
  have hk : ρ.dual (k : G)⁻¹ ℓ = ℓ :=
    hK ⟨(k : G)⁻¹, K.inv_mem k.property.1⟩
  have hl : ρ (l : G) v = v := hL ⟨(l : G), l.property.2⟩
  rw [matrixCoefficient_mul, hl, matrixCoefficient_mul_left, hk]

theorem matrixCoefficient_isLocallyConstant [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation R G V) (ℓ : Module.Dual R V) (v : V)
    (hv : IsSmoothVector ρ v) : IsLocallyConstant (matrixCoefficient ρ ℓ v) := by
  obtain ⟨K, hK⟩ := hv
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  refine ⟨(fun h : G => g⁻¹ * h) ⁻¹' (K : Set G),
    K.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro h hh
    have hfix : ρ (g⁻¹ * h) v = v := hK ⟨g⁻¹ * h, hh⟩
    calc
      matrixCoefficient ρ ℓ v h = matrixCoefficient ρ ℓ v (g * (g⁻¹ * h)) := by
        simp
      _ = matrixCoefficient ρ ℓ (ρ (g⁻¹ * h) v) g :=
        matrixCoefficient_mul ρ ℓ v g (g⁻¹ * h)
      _ = matrixCoefficient ρ ℓ v g := by rw [hfix]

theorem matrixCoefficientLaws :
    MatrixCoefficientLawsStatement (R := R) (G := G) (V := V) (W := W) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ ℓ v g h
    exact ⟨matrixCoefficient_mul ρ ℓ v g h, matrixCoefficient_mul_left ρ ℓ v g h⟩
  · intro ρ σ f ℓ v
    exact matrixCoefficient_intertwining f ℓ v
  · intro _ ρ ℓ v hℓ hv
    exact matrixCoefficient_biInvariant ρ ℓ v hℓ hv
  · intro _ _ ρ ℓ v hv
    exact matrixCoefficient_isLocallyConstant ρ ℓ v hv

end Langlands
