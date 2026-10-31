import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.Smooth.Transfer.GroupEquivalence
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Transport of the actual bi-smooth coefficient space

Continuous group isomorphisms transport both smooth vectors and smooth
functionals. Representation equivalences preserve the coefficient submodule.
Inverse transpose therefore gives the published transformed value family of
the original representation as the ordinary value family of its pullback.
-/

noncomputable section

namespace Langlands.GodementJacquet

universe uG uH uV uW uF

section GroupTransport

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Linear precomposition of scalar functions by a group homomorphism. -/
def coefficientPullback (φ : H →* G) : (G → ℂ) →ₗ[ℂ] (H → ℂ) where
  toFun f := f ∘ φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] [TopologicalSpace H] in
@[simp]
theorem coefficientPullback_apply (φ : H →* G) (f : G → ℂ) (h : H) :
    coefficientPullback φ f h = f (φ h) := rfl

/-- The same smooth functional is smooth for a continuous pullback. -/
def smoothDualPullback (σ : Representation ℂ G V) (φ : H →* G)
    (hφ : Continuous φ) (ℓ : SmoothDual σ) : SmoothDual (σ.comp φ) :=
  ⟨ℓ.val, by
    rw [dual_comp_monoidHom]
    exact isSmoothVector_comp φ hφ ℓ.property⟩

/-- Continuous pullback sends every actual bi-smooth coefficient to one of
the pulled-back representation. This includes finite linear combinations. -/
theorem map_biSmoothMatrixCoefficients_le (σ : Representation ℂ G V)
    (φ : H →* G) (hφ : Continuous φ) :
    (biSmoothMatrixCoefficients σ).map (coefficientPullback φ) ≤
      biSmoothMatrixCoefficients (σ.comp φ) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro f ⟨ℓ, v, rfl⟩
  exact Submodule.subset_span
    ⟨smoothDualPullback σ φ hφ ℓ,
      ⟨v.val, isSmoothVector_comp φ hφ v.property⟩, rfl⟩

/-- A continuous group isomorphism transports the entire coefficient space,
with no smoothness or admissibility hypothesis on the ambient action. -/
theorem biSmoothMatrixCoefficients_comp_equiv (σ : Representation ℂ G V)
    (e : H ≃ₜ* G) :
    biSmoothMatrixCoefficients (σ.comp e.toMonoidHom) =
      (biSmoothMatrixCoefficients σ).map (coefficientPullback e.toMonoidHom) := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (map_biSmoothMatrixCoefficients_le σ e.toMonoidHom e.continuous)
  rintro f ⟨ℓ, v, rfl⟩
  let ℓ' : SmoothDual σ :=
    ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff σ e ℓ.val).mp ℓ.property⟩
  let v' : smoothVectors σ :=
    ⟨v.val, (isSmoothVector_comp_continuousMulEquiv_iff σ e v.val).mp v.property⟩
  exact Submodule.mem_map.mpr
    ⟨biSmoothCoefficient σ ℓ' v', Submodule.subset_span ⟨ℓ', v', rfl⟩, rfl⟩

/-- Universal assertions on pulled-back coefficients can be expressed using
the original family. The map equality supplies both directions. -/
theorem forall_biSmoothMatrixCoefficients_comp_equiv
    (σ : Representation ℂ G V) (e : H ≃ₜ* G) (Q : (H → ℂ) → Prop) :
    (∀ f : biSmoothMatrixCoefficients (σ.comp e.toMonoidHom), Q f.val) ↔
      ∀ f : biSmoothMatrixCoefficients σ,
        Q (coefficientPullback e.toMonoidHom f.val) := by
  constructor
  · intro h f
    exact h ⟨_, map_biSmoothMatrixCoefficients_le σ e.toMonoidHom e.continuous
      (Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩)⟩
  · intro h ⟨f, hf⟩
    rw [biSmoothMatrixCoefficients_comp_equiv] at hf
    obtain ⟨f', hf', rfl⟩ := Submodule.mem_map.mp hf
    exact h ⟨f', hf'⟩

end GroupTransport

section RepresentationTransport

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {τ : Representation ℂ G W}

private theorem biSmoothMatrixCoefficients_le_of_equiv (e : σ.Equiv τ) :
    biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ := by
  apply Submodule.span_le.mpr
  rintro f ⟨ℓ, v, rfl⟩
  let ℓ' : SmoothDual σ :=
    ⟨dualEquiv e ℓ.val, isSmoothVector_map (dualEquiv e).toIntertwiningMap ℓ.property⟩
  let v' : smoothVectors σ :=
    ⟨e.symm v.val, isSmoothVector_map e.symm.toIntertwiningMap v.property⟩
  apply Submodule.subset_span
  refine ⟨ℓ', v', funext fun g => ?_⟩
  change ℓ.val (e (σ g (e.symm v.val))) = ℓ.val (τ g v.val)
  apply congrArg ℓ.val
  calc
    e (σ g (e.symm v.val)) = τ g (e (e.symm v.val)) :=
      Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g _
    _ = τ g v.val := by rw [e.apply_symm_apply]

/-- Representation equivalences preserve the actual coefficient submodule,
including its smooth-functional and smooth-vector conditions. -/
theorem biSmoothMatrixCoefficients_equiv (e : σ.Equiv τ) :
    biSmoothMatrixCoefficients σ = biSmoothMatrixCoefficients τ :=
  le_antisymm (biSmoothMatrixCoefficients_le_of_equiv e.symm)
    (biSmoothMatrixCoefficients_le_of_equiv e)

end RepresentationTransport

section MatrixTransport

open MeasureTheory RankinSelberg

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (abv : AbsoluteValue F ℝ)
  (μ : Measure (Langlands.GeneralLinear (n + 1) F))
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

theorem matrixRationalValues_equiv (e : σ.Equiv τ) :
    matrixRationalValues q abv μ σ = matrixRationalValues q abv μ τ := by
  unfold matrixRationalValues
  rw [biSmoothMatrixCoefficients_equiv e]

theorem iotaMatrixRationalValues_equiv (e : σ.Equiv τ) :
    iotaMatrixRationalValues q abv μ σ = iotaMatrixRationalValues q abv μ τ := by
  unfold iotaMatrixRationalValues
  rw [biSmoothMatrixCoefficients_equiv e]

theorem matrixAnalyticAssertions_equiv (e : σ.Equiv τ) (P : Polynomial ℂ) :
    MatrixAnalyticAssertions q abv μ σ P ↔ MatrixAnalyticAssertions q abv μ τ P := by
  unfold MatrixAnalyticAssertions MatrixConvergesOnRight IsMatrixNormalizedGenerator
    matrixRationalValues
  rw [biSmoothMatrixCoefficients_equiv e]

theorem iotaMatrixAnalyticAssertions_equiv (e : σ.Equiv τ) (P : Polynomial ℂ) :
    IotaMatrixAnalyticAssertions q abv μ σ P ↔
      IotaMatrixAnalyticAssertions q abv μ τ P := by
  unfold IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight
    IsIotaMatrixNormalizedGenerator iotaMatrixRationalValues
  rw [biSmoothMatrixCoefficients_equiv e]

/-- The transformed rational-value family is the ordinary family of the actual
inverse-transpose pullback, without identifying it with a contragredient. -/
theorem iotaMatrixRationalValues_eq_comp_inverseTranspose :
    iotaMatrixRationalValues q abv μ σ =
      matrixRationalValues q abv μ
        (σ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom) := by
  ext R
  constructor
  · rintro ⟨Φ, f, hR⟩
    exact ⟨Φ, ⟨_, map_biSmoothMatrixCoefficients_le σ
      (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom
      (GeneralLinear.continuous_inverseTranspose _ _)
      (Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩)⟩, hR⟩
  · rintro ⟨Φ, f, hR⟩
    have hf := f.property
    change f.val ∈ biSmoothMatrixCoefficients
      (σ.comp (GeneralLinear.inverseTransposeContinuous (n + 1) F).toMonoidHom) at hf
    rw [biSmoothMatrixCoefficients_comp_equiv σ
      (GeneralLinear.inverseTransposeContinuous (n + 1) F)] at hf
    obtain ⟨f', hf', hff⟩ := Submodule.mem_map.mp hf
    rw [← hff] at hR
    exact ⟨Φ, ⟨f', hf'⟩, hR⟩

/-- The full transformed predicate is the ordinary analytic predicate of the
inverse-transpose pullback. The same bound, tests, measure and polynomial are
retained. -/
theorem iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose (P : Polynomial ℂ) :
    IotaMatrixAnalyticAssertions q abv μ σ P ↔
      MatrixAnalyticAssertions q abv μ
        (σ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom) P := by
  have hforall := forall_biSmoothMatrixCoefficients_comp_equiv σ
    (GeneralLinear.inverseTransposeContinuous (n + 1) F)
  have hconverges :
      IotaMatrixConvergesOnRight abv μ σ ↔
        MatrixConvergesOnRight abv μ
          (σ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom) := by
    unfold IotaMatrixConvergesOnRight MatrixConvergesOnRight
    apply exists_congr
    intro a
    apply forall_congr'
    intro Φ
    exact (hforall (fun f => ∀ s : ℂ, a < s.re →
      MatrixConverges abv μ Φ (s + jpssShift n) f)).symm
  have hrational :
      (∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients σ,
        ∃ R, HasShiftedRationalValue q abv μ Φ (coefficientIota f.val) R) ↔
      (∀ Φ : MatrixTestFunction n F,
        ∀ f : biSmoothMatrixCoefficients
          (σ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom),
        ∃ R, HasShiftedRationalValue q abv μ Φ f.val R) := by
    apply forall_congr'
    intro Φ
    exact (hforall (fun f => ∃ R, HasShiftedRationalValue q abv μ Φ f R)).symm
  unfold IotaMatrixAnalyticAssertions MatrixAnalyticAssertions
  rw [hconverges, hrational]
  unfold IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator
  rw [iotaMatrixRationalValues_eq_comp_inverseTranspose]

end MatrixTransport

end Langlands.GodementJacquet
