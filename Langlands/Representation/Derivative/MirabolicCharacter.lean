import Langlands.Group.GL.MirabolicRadical
import Langlands.Group.GL.Nonarchimedean
import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # The positive Bernstein–Zelevinsky character on the actual mirabolic radical -/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF

variable {F : Type uF} [CommRing F]

/-- The last additive coordinate of the radical `V_(n+2)`, written multiplicatively. -/
def lastCoordinate (n : ℕ) : radical (n + 1) F →* Multiplicative F :=
  ({ toFun := fun v : Fin (n + 1) → F => v (Fin.last n)
     map_zero' := rfl
     map_add' := fun _ _ => rfl } : (Fin (n + 1) → F) →+ F).toMultiplicative.comp
    radicalEquiv.toMonoidHom

@[simp] theorem lastCoordinate_apply (n : ℕ) (u : radical (n + 1) F) :
    (lastCoordinate n u).toAdd = radicalCoordinates u (Fin.last n) := rfl

variable [TopologicalSpace F]

/-- The positive character `theta(u(v)) = psi(v_last)`; no inverse is inserted. -/
def theta (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : radical (n + 1) F →* ℂˣ :=
  Circle.toUnits.comp (ψ.toAddChar.toMonoidHom.comp (lastCoordinate n))

@[simp] theorem theta_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (u : radical (n + 1) F) :
    (theta ψ n u : ℂ) = ψ.complex (radicalCoordinates u (Fin.last n)) := rfl

@[simp] theorem theta_radicalElement (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (v : Fin (n + 1) → F) :
    (theta ψ n (radicalElement v) : ℂ) = ψ.complex (v (Fin.last n)) := by
  simp

@[simp] theorem norm_theta (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (u : radical (n + 1) F) : ‖(theta ψ n u : ℂ)‖ = 1 := by
  simp

omit [TopologicalSpace F] in
/-- The last row of the actual smaller mirabolic fixes the last coordinate. -/
theorem mulVec_last (n : ℕ) (g : mirabolic n F) (v : Fin (n + 1) → F) :
    (g.val.val.mulVec v) (Fin.last n) = v (Fin.last n) := by
  have hg : ∀ j, g.val.val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
    g.property
  simp [Matrix.mulVec, dotProduct, hg]

/-- Exact invariance for character localization under the actual successor range. -/
theorem theta_isInvariant (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Jacquet.Localization.IsInvariant (radical (n + 1) F) (successorSubgroup n F)
      successorSubgroup_le_normalizer (theta ψ n) := by
  intro m u
  obtain ⟨m, rfl⟩ := successorEquiv.surjective m
  obtain ⟨v, rfl⟩ := radicalEquiv.symm.surjective u
  have he : Jacquet.Localization.conjugate (radical (n + 1) F)
      (successorSubgroup n F) successorSubgroup_le_normalizer
      (successorEquiv m) (radicalEquiv.symm v) =
      radicalElement (m.val.val.mulVec v.toAdd) := by
    apply Subtype.ext
    change levi m.val * (radicalElement v.toAdd).val * (levi m.val)⁻¹ = _
    exact levi_conjugate_radicalElement m.val v.toAdd
  rw [he]
  apply Units.ext
  simp only [radicalEquiv_symm_apply, theta_radicalElement, mulVec_last]

omit [TopologicalSpace F] in
/-- Only the final adjacent entry survives on a radical matrix. -/
theorem superdiagonalSum_radical (n : ℕ) (u : radical (n + 1) F) :
    (∑ i : Fin (n + 1), u.val.val.val i.castSucc i.succ) =
      radicalCoordinates u (Fin.last n) := by
  rw [Fin.sum_univ_castSucc]
  have hz : (∑ i : Fin n,
      u.val.val.val i.castSucc.castSucc i.castSucc.succ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    change u.val.val.val i.castSucc.castSucc i.succ.castSucc = 0
    rw [u.property _ i.succ]
    have hne : i.castSucc.castSucc ≠ i.succ.castSucc :=
      fun h => (ne_of_lt i.castSucc_lt_succ) (Fin.castSucc_injective _ h)
    exact ite_eq_right hne
  rw [hz, zero_add]
  rfl

/-- Literal equality with the restriction of the published positive Whittaker character. -/
theorem theta_eq_standardCharacter_comp (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    theta ψ n = (Whittaker.standardCharacter ψ (n + 1)).comp radicalToUpperUnipotent := by
  ext u
  change ψ.complex (radicalCoordinates u (Fin.last n)) =
    ψ.complex (∑ i : Fin (n + 1), u.val.val.val i.castSucc i.succ)
  rw [superdiagonalSum_radical]

/-- Continuity holds for every coefficient topology; it uses extracted entries only. -/
def thetaContinuous (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    ContinuousMonoidHom (radical (n + 1) F) ℂˣ where
  toMonoidHom := theta ψ n
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    have hc : Continuous (fun u : radical (n + 1) F =>
        ψ (radicalCoordinates u (Fin.last n))) :=
      ψ.continuous_toFun.comp ((continuous_apply (Fin.last n)).comp continuous_radicalCoordinates)
    exact ⟨continuous_subtype_val.comp hc, continuous_subtype_val.comp hc.inv⟩

/-- The open-kernel criterion applies directly to this actual matrix character. -/
theorem theta_isOpen_ker (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    [NonarchimedeanGroup (radical (n + 1) F)] :
    IsOpen ((theta ψ n).ker : Set (radical (n + 1) F)) :=
  Langlands.isOpen_ker_of_continuous_complex_character _ (thetaContinuous ψ n).continuous

end Langlands.Derivative.Mirabolic

namespace Langlands.PadicField.TopologicalData

open GeneralLinear.Mirabolic HarmonicAnalysis

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The BZ character for every supplied p-adic topological realization. -/
def mirabolicTheta (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    radical (n + 1) F.Carrier →* ℂˣ := by
  letI := T.topology
  exact Derivative.Mirabolic.theta ψ n

/-- The same character as a continuous homomorphism for the supplied topology. -/
def mirabolicThetaContinuous (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (radical (n + 1) F.Carrier) ℂˣ := by
  letI := T.topology
  exact Derivative.Mirabolic.thetaContinuous ψ n

/-- The actual character kernel is open for every supplied p-adic topology. -/
theorem mirabolicTheta_isOpen_ker (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    IsOpen ((T.mirabolicTheta ψ n).ker : Set (radical (n + 1) F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : NonarchimedeanGroup (GeneralLinear (n + 1 + 1) F.Carrier) :=
    valuativeGeneralLinearNonarchimedean F.Carrier (n + 1 + 1)
  exact Derivative.Mirabolic.theta_isOpen_ker ψ n

end Langlands.PadicField.TopologicalData
