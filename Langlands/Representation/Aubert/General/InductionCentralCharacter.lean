import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Ambient central characters of actual normalized induction -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Aubert.General

universe uG uV

section Center

variable {G : Type uG} [Group G] (M : Subgroup G)
  (hZM : Subgroup.center G ≤ M)

/-- The literal ambient central element, viewed in the full center of a
subgroup containing the ambient center. -/
def ambientCenterToLeviCenter : Subgroup.center G →* Subgroup.center M where
  toFun z := ⟨⟨z, hZM z.property⟩, by
    apply Subgroup.mem_center_iff.mpr
    intro m
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp z.property m⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem ambientCenterToLeviCenter_coe (z : Subgroup.center G) :
    (((ambientCenterToLeviCenter M hZM z : Subgroup.center M) : M) : G) = z := rfl

variable [TopologicalSpace G]

theorem continuous_ambientCenterToLeviCenter :
    Continuous (ambientCenterToLeviCenter M hZM) :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The scalar central character inherited from the actual inducing Levi. -/
def normalizedInductionCentralCharacter (χ : Subgroup.center M →* ℂˣ) :
    Subgroup.center G →* ℂˣ :=
  χ.comp (ambientCenterToLeviCenter M hZM)

theorem isOpen_ker_normalizedInductionCentralCharacter
    (χ : Subgroup.center M →* ℂˣ) (hχ : IsOpen (χ.ker : Set (Subgroup.center M))) :
    IsOpen ((normalizedInductionCentralCharacter M hZM χ).ker :
      Set (Subgroup.center G)) :=
  hχ.preimage (continuous_ambientCenterToLeviCenter M hZM)

end Center

section Modulus

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- Conjugation by an ambient central point has Haar modulus one on every
closed normalized subgroup. -/
theorem closedRestrictCharacter_eq_one_of_mem_center
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M)
    (hm : (m : G) ∈ Subgroup.center G) :
    HaarModulus.closedRestrictCharacter U hU M hMU m = 1 := by
  let := hU.locallyCompactSpace
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  have he : HaarModulus.normalizerConj U ⟨m, hMU m.property⟩ =
      ContinuousMulEquiv.refl U := by
    ext u
    change (m : G) * (u : G) * (m : G)⁻¹ = u
    rw [← Subgroup.mem_center_iff.mp hm (u : G), mul_inv_cancel_right]
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar
    (HaarModulus.normalizerConj U ⟨m, hMU m.property⟩) = 1
  rw [he, MeasureTheory.mulEquivHaarChar_refl]

theorem closedHalfCharacter_eq_one_of_mem_center
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M)
    (hm : (m : G) ∈ Subgroup.center G) :
    HaarModulus.closedHalfCharacter U hU M hMU m = 1 := by
  apply Units.ext
  change ((NNReal.sqrt
    (HaarModulus.closedRestrictCharacter U hU M hMU m : ℝ≥0) : ℝ) : ℂ) = 1
  rw [closedRestrictCharacter_eq_one_of_mem_center U M hU hMU m hm]
  simp

end Modulus

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hZM : Subgroup.center G ≤ M)

/-- Right translation by a central element is the inducing scalar action;
the positive half modulus contributes one. -/
theorem normalizedInductionCentralCharacter_acts
    (A : SmoothRep.{0, uG, uV} ℂ M) (χ : Subgroup.center M →* ℂˣ)
    (hact : ∀ (z : Subgroup.center M) (v : A),
      A.representation z v = (χ z : ℂ) • v)
    (z : Subgroup.center G) (f : (normalizedInductionFunctor h hU).obj A) :
    ((normalizedInductionFunctor h hU).obj A).representation z f =
      (normalizedInductionCentralCharacter M hZM χ z : ℂ) • f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change Induction.eval P (inducingRepresentation h hU A) f (x * (z : G)) =
    (normalizedInductionCentralCharacter M hZM χ z : ℂ) •
      Induction.eval P (inducingRepresentation h hU A) f x
  rw [Subgroup.mem_center_iff.mp z.property x]
  let m : M := ⟨z, hZM z.property⟩
  let p : P := ⟨m, h.levi_le m.property⟩
  change Induction.eval P (inducingRepresentation h hU A) f ((p : G) * x) = _
  rw [normalizedInductionFunctor_covariant h hU A f p x,
    closedHalfCharacter_eq_one_of_mem_center U P hU h.le_normalizer p z.property,
    Units.val_one, one_smul, h.projection_levi]
  exact hact (ambientCenterToLeviCenter M hZM z) _

/-- A unitary central character on the inducing representation restricts to
the actual full ambient center on normalized induction. -/
def normalizedInductionUnitaryCentralCharacter
    (A : SmoothRep.{0, uG, uV} ℂ M) (c : UnitaryCentralCharacter A.representation) :
    UnitaryCentralCharacter
      ((normalizedInductionFunctor h hU).obj A).representation where
  character := normalizedInductionCentralCharacter M hZM c.character
  isOpen_ker := isOpen_ker_normalizedInductionCentralCharacter M hZM _ c.isOpen_ker
  norm_eq_one z := c.norm_eq_one (ambientCenterToLeviCenter M hZM z)
  acts := normalizedInductionCentralCharacter_acts h hU hZM A c.character c.acts

end Induction

end Langlands.Aubert.General
