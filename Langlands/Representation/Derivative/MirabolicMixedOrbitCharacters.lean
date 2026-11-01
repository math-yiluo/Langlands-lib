import Langlands.Group.GL.MirabolicMixedOrbitRadicals
import Langlands.Representation.Derivative.MirabolicCharacter

/-! Character calculations on the actual mixed-orbit radical intersections. -/

noncomputable section

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.HarmonicAnalysis

universe u uV uW

variable (k r : ℕ) {R : Type u} [CommRing R]

/-- The mirabolic coefficient of a left radical-intersection element is radical. -/
theorem leftRadicalCoefficient_mem_radical (i : Fin 2)
    (u : leftRadicalIntersection k r R i) :
    (leftRadicalCoefficient k r R i u).2 ∈ radical (r + 1) R := by
  have hu : u = leftOrbitRadicalElement k r i (radicalCoordinates u.val) := by
    apply Subtype.ext
    exact (radicalElement_coordinates u.val).symm
  rw [hu, leftRadicalCoefficient_element]
  exact (radicalElement _).property

/-- The actual source-radical homomorphism at a left representative. -/
def leftRadicalSource (i : Fin 2) :
    leftRadicalIntersection k r R i →* radical (r + 1) R where
  toFun u := ⟨(leftRadicalCoefficient k r R i u).2,
    leftRadicalCoefficient_mem_radical k r i u⟩
  map_one' := Subtype.ext (congrArg Prod.snd (map_one (leftRadicalCoefficient k r R i)))
  map_mul' u v :=
    Subtype.ext (congrArg Prod.snd (map_mul (leftRadicalCoefficient k r R i) u v))

/-- The mirabolic coefficient of a right radical-intersection element is radical. -/
theorem rightRadicalCoefficient_mem_radical (i : Fin 2)
    (u : rightRadicalIntersection k r R i) :
    (rightRadicalCoefficient k r R i u).1 ∈ radical (r + 1) R := by
  have hu : u = rightOrbitRadicalElement k r i (radicalCoordinates u.val)
      (by rw [radicalElement_coordinates]; exact u.property) := by
    apply Subtype.ext
    exact (radicalElement_coordinates u.val).symm
  rw [hu, rightRadicalCoefficient_element]
  exact (radicalElement _).property

/-- The actual source-radical homomorphism at a right representative. -/
def rightRadicalSource (i : Fin 2) :
    rightRadicalIntersection k r R i →* radical (r + 1) R where
  toFun u := ⟨(rightRadicalCoefficient k r R i u).1,
    rightRadicalCoefficient_mem_radical k r i u⟩
  map_one' := Subtype.ext (congrArg Prod.fst (map_one (rightRadicalCoefficient k r R i)))
  map_mul' u v :=
    Subtype.ext (congrArg Prod.fst (map_mul (rightRadicalCoefficient k r R i) u v))

/-- The other factor of the actual left coefficient is identically the identity. -/
theorem leftRadicalCoefficient_eq (i : Fin 2)
    (u : leftRadicalIntersection k r R i) :
    leftRadicalCoefficient k r R i u = (1, (leftRadicalSource k r i u).val) := by
  apply Prod.ext
  · have hu : u = leftOrbitRadicalElement k r i (radicalCoordinates u.val) := by
      apply Subtype.ext
      exact (radicalElement_coordinates u.val).symm
    rw [hu, leftRadicalCoefficient_element]
  · rfl

/-- The other factor of the actual right coefficient is identically the identity. -/
theorem rightRadicalCoefficient_eq (i : Fin 2)
    (u : rightRadicalIntersection k r R i) :
    rightRadicalCoefficient k r R i u = ((rightRadicalSource k r i u).val, 1) := by
  apply Prod.ext
  · rfl
  · have hu : u = rightOrbitRadicalElement k r i (radicalCoordinates u.val)
        (by rw [radicalElement_coordinates]; exact u.property) := by
      apply Subtype.ext
      exact (radicalElement_coordinates u.val).symm
    rw [hu, rightRadicalCoefficient_element]

@[simp] theorem leftRadicalSource_element (i : Fin 2) (v : Fin (k + r + 2) → R) :
    leftRadicalSource k r i (leftOrbitRadicalElement k r i v) =
      radicalElement (fun j : Fin (r + 1) =>
        leftRadicalColumn k r i v ⟨k + 1 + j.val, by omega⟩) := by
  apply Subtype.ext
  exact congrArg Prod.snd (leftRadicalCoefficient_element k r i v)

@[simp] theorem rightRadicalSource_element (i : Fin 2) (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R i) :
    rightRadicalSource k r i (rightOrbitRadicalElement k r i v hv) =
      radicalElement (fun j : Fin (r + 1) =>
        rightRadicalColumn k r i v ⟨j.val, by omega⟩) := by
  apply Subtype.ext
  exact congrArg Prod.fst (rightRadicalCoefficient_element k r i v hv)

variable [TopologicalSpace R] (ψ : UnitaryAdditiveCharacter R)

section Topology

variable [IsTopologicalRing R]

theorem continuous_leftRadicalSource (i : Fin 2) :
    Continuous (leftRadicalSource k r (R := R) i) :=
  continuous_induced_rng.mpr (continuous_snd.comp (continuous_leftRadicalCoefficient k r R i))

theorem continuous_rightRadicalSource (i : Fin 2) :
    Continuous (rightRadicalSource k r (R := R) i) :=
  continuous_induced_rng.mpr (continuous_fst.comp (continuous_rightRadicalCoefficient k r R i))

end Topology

/-- The ambient positive character restricted to the left radical intersection. -/
def leftOrbitTheta (i : Fin 2) : leftRadicalIntersection k r R i →* ℂˣ :=
  (Langlands.Derivative.Mirabolic.theta ψ (k + r + 1)).comp
    (leftRadicalIntersection k r R i).subtype

/-- The ambient positive character restricted to the right radical intersection. -/
def rightOrbitTheta (i : Fin 2) : rightRadicalIntersection k r R i →* ℂˣ :=
  (Langlands.Derivative.Mirabolic.theta ψ (k + r + 1)).comp
    (rightRadicalIntersection k r R i).subtype

@[simp] theorem leftOrbitTheta_element (i : Fin 2) (v : Fin (k + r + 2) → R) :
    (leftOrbitTheta k r ψ i (leftOrbitRadicalElement k r i v) : ℂ) =
      ψ.complex (v (Fin.last (k + r + 1))) :=
  Langlands.Derivative.Mirabolic.theta_radicalElement ψ (k + r + 1) v

@[simp] theorem rightOrbitTheta_element (i : Fin 2) (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R i) :
    (rightOrbitTheta k r ψ i (rightOrbitRadicalElement k r i v hv) : ℂ) =
      ψ.complex (v (Fin.last (k + r + 1))) :=
  Langlands.Derivative.Mirabolic.theta_radicalElement ψ (k + r + 1) v

/-- At the left identity orbit the ambient positive character is exactly
the source positive character, pulled back by the actual coefficient. -/
theorem leftOrbitTheta_one :
    leftOrbitTheta k r ψ 1 =
      (Langlands.Derivative.Mirabolic.theta ψ r).comp (leftRadicalSource k r 1) := by
  ext u
  obtain ⟨v, hv⟩ := radicalEquiv.symm.surjective u.val
  have hu : u = leftOrbitRadicalElement k r 1 v.toAdd := by
    apply Subtype.ext
    exact hv.symm
  rw [hu]
  change (leftOrbitTheta k r ψ 1 (leftOrbitRadicalElement k r 1 v.toAdd) : ℂ) =
    (Langlands.Derivative.Mirabolic.theta ψ r
      (leftRadicalSource k r 1 (leftOrbitRadicalElement k r 1 v.toAdd)) : ℂ)
  rw [leftOrbitTheta_element]
  have hs : leftRadicalSource k r 1 (leftOrbitRadicalElement k r 1 v.toAdd) =
      radicalElement (fun j : Fin (r + 1) =>
        v.toAdd ⟨k + 1 + j.val, by omega⟩) :=
    Subtype.ext (congrArg Prod.snd (leftRadicalCoefficient_one k r v.toAdd))
  rw [hs, Langlands.Derivative.Mirabolic.theta_radicalElement]
  have hi : (⟨k + 1 + (Fin.last r).val, by omega⟩ : Fin (k + r + 2)) =
      Fin.last (k + r + 1) := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  rw [hi]

/-- At the right cycle orbit the ambient positive character is exactly
the source positive character, pulled back by the actual coefficient. -/
theorem rightOrbitTheta_zero :
    rightOrbitTheta k r ψ 0 =
      (Langlands.Derivative.Mirabolic.theta ψ r).comp (rightRadicalSource k r 0) := by
  ext u
  let v := radicalCoordinates u.val
  have hv : radicalElement v ∈ rightRadicalIntersection k r R 0 := by
    rw [radicalElement_coordinates]
    exact u.property
  have hu : u = rightOrbitRadicalElement k r 0 v hv := by
    apply Subtype.ext
    exact (radicalElement_coordinates u.val).symm
  rw [hu]
  change (rightOrbitTheta k r ψ 0 (rightOrbitRadicalElement k r 0 v hv) : ℂ) =
    (Langlands.Derivative.Mirabolic.theta ψ r
      (rightRadicalSource k r 0 (rightOrbitRadicalElement k r 0 v hv)) : ℂ)
  rw [rightOrbitTheta_element]
  have hs : rightRadicalSource k r 0 (rightOrbitRadicalElement k r 0 v hv) =
      radicalElement (fun j : Fin (r + 1) =>
        if j.val = r then v (Fin.last (k + r + 1))
        else v ⟨j.val, by omega⟩) :=
    Subtype.ext (congrArg Prod.fst (rightRadicalCoefficient_zero k r v hv))
  rw [hs, Langlands.Derivative.Mirabolic.theta_radicalElement]
  simp only [Fin.val_last, ↓reduceIte]

/-- The ambient positive character is trivial on the right identity intersection. -/
theorem rightOrbitTheta_one : rightOrbitTheta k r ψ 1 = 1 := by
  ext u
  let v := radicalCoordinates u.val
  have hv : radicalElement v ∈ rightRadicalIntersection k r R 1 := by
    rw [radicalElement_coordinates]
    exact u.property
  have hu : u = rightOrbitRadicalElement k r 1 v hv := by
    apply Subtype.ext
    exact (radicalElement_coordinates u.val).symm
  rw [hu]
  change (rightOrbitTheta k r ψ 1 (rightOrbitRadicalElement k r 1 v hv) : ℂ) = 1
  rw [rightOrbitTheta_element, rightRadicalIntersection_one_terminal_zero k r v hv]
  simp

/-- At the left cycle there is a radical element invisible to the entire
coefficient group and detected by the ambient positive character. -/
theorem exists_leftOrbitTheta_zero_ne_one :
    ∃ u : leftRadicalIntersection k r R 0,
      leftRadicalCoefficient k r R 0 u = 1 ∧ (leftOrbitTheta k r ψ 0 u : ℂ) ≠ 1 := by
  obtain ⟨c, hc⟩ : ∃ c : R, ψ.complex c ≠ 1 := by
    by_contra h
    push Not at h
    apply ψ.nontrivial
    ext c
    have := h c
    rw [UnitaryAdditiveCharacter.complex_apply] at this
    rw [AddChar.one_apply]
    exact this.trans Circle.coe_one.symm
  refine ⟨leftOrbitRadicalElement k r 0 (terminalRadicalColumn (k + r + 1) c),
    leftRadicalCoefficient_terminal k r c, ?_⟩
  simpa only [leftOrbitTheta_element, terminalRadicalColumn_last] using hc

/-- Every linear map equivariant from the actual left-cycle coefficient to the
ambient positive character is zero, for arbitrary coefficient representations. -/
theorem leftOrbitTheta_zero_equivariant_eq_zero
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear (k + 1) R × mirabolic (r + 1) R) V)
    (f : V →ₗ[ℂ] W)
    (hf : ∀ (u : leftRadicalIntersection k r R 0) (v : V),
      f (σ (leftRadicalCoefficient k r R 0 u) v) =
        (leftOrbitTheta k r ψ 0 u : ℂ) • f v) :
    f = 0 := by
  obtain ⟨u, hu, hθ⟩ := exists_leftOrbitTheta_zero_ne_one k r ψ
  ext v
  change f v = 0
  have he : f v = (leftOrbitTheta k r ψ 0 u : ℂ) • f v := by
    simpa only [hu, map_one, Module.End.one_apply] using hf u v
  have hz : ((leftOrbitTheta k r ψ 0 u : ℂ) - 1) • f v = 0 := by
    rw [sub_smul, one_smul, ← he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hθ)

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
