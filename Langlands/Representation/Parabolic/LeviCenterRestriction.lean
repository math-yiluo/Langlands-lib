import Langlands.Representation.Classification.ProductLeviCentralCharacter

/-!
# Restricting a Levi central character to the ambient center

The diagonal-block projection restricts to a continuous homomorphism from the
full ambient center to the full Levi center. A compatible ambient scalar action
therefore carries the pulled-back smooth unitary central character.
-/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

universe uR uV uW

variable {n : ℕ} (B : BlockShape n) (R : Type uR) [CommRing R]

/-- A common scalar in every Levi block, with its centrality certificate. -/
def diagonalScalarToCenter : Rˣ →* Subgroup.center (B.Levi R) :=
  (B.blockScalarToCenter R).comp
    { toFun := fun a _ => a
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp]
theorem diagonalScalarToCenter_val (a : Rˣ) :
    (B.diagonalScalarToCenter R a).val =
      fun i => GeneralLinear.scalar (n := B.size i) a := rfl

theorem leviEmbedding_diagonalScalar (a : Rˣ) :
    B.leviEmbedding R (fun i => GeneralLinear.scalar (n := B.size i) a) =
      GeneralLinear.scalar (n := n) a := by
  change B.blockScalar R (fun _ => a) = _
  apply Units.ext
  rw [B.coe_blockScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

private theorem center_le_parabolic :
    Subgroup.center (GeneralLinear n R) ≤ B.parabolic R := by
  intro z hz
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨a, rfl⟩ := hz
  rw [← B.leviEmbedding_diagonalScalar R a]
  exact (B.leviInParabolic R _).property

/-- The full ambient center included in the actual block parabolic. -/
def centerToParabolic :
    Subgroup.center (GeneralLinear n R) →* B.parabolic R :=
  (Subgroup.center (GeneralLinear n R)).subtype.codRestrict _
    (fun z => B.center_le_parabolic R z.property)

@[simp]
theorem centerToParabolic_scalar (a : Rˣ) :
    B.centerToParabolic R (GeneralLinear.scalarToCenter a) =
      B.leviInParabolic R
        (fun i => GeneralLinear.scalar (n := B.size i) a) := by
  apply Subtype.ext
  exact (B.leviEmbedding_diagonalScalar R a).symm

/-- Restriction of the actual diagonal-block projection to the full centers. -/
def centerToLeviCenter :
    Subgroup.center (GeneralLinear n R) →* Subgroup.center (B.Levi R) :=
  ((B.leviProjection R).comp (B.centerToParabolic R)).codRestrict _ (by
    intro z
    have hz := z.property
    simp only [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨a, ha⟩ := hz
    have he : z = GeneralLinear.scalarToCenter a := Subtype.ext ha.symm
    rw [he, MonoidHom.comp_apply, B.centerToParabolic_scalar, B.leviProjection_section]
    exact (B.diagonalScalarToCenter R a).property)

@[simp]
theorem centerToLeviCenter_scalar (a : Rˣ) :
    B.centerToLeviCenter R (GeneralLinear.scalarToCenter a) =
      B.diagonalScalarToCenter R a := by
  apply Subtype.ext
  change B.leviProjection R (B.centerToParabolic R
    (GeneralLinear.scalarToCenter a)) = _
  rw [B.centerToParabolic_scalar, B.leviProjection_section]
  rfl

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The full-center map has the actual subgroup topologies. -/
def centerToLeviCenterContinuous :
    ContinuousMonoidHom (Subgroup.center (GeneralLinear n R))
      (Subgroup.center (B.Levi R)) where
  toMonoidHom := B.centerToLeviCenter R
  continuous_toFun := by
    have hp : Continuous (B.centerToParabolic R) :=
      continuous_subtype_val.subtype_mk _
    exact ((B.leviProjectionContinuous R).continuous.comp hp).subtype_mk _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Pull a Levi unitary central character back to any ambient action having
the corresponding common-scalar action. No nonzero-carrier premise is needed. -/
def unitaryCentralCharacterOfLeviScalar
    (σ : Representation ℂ (B.Levi R) V)
    (c : UnitaryCentralCharacter σ)
    (ρ : Representation ℂ (GeneralLinear n R) W)
    (hact : ∀ (a : Rˣ) (w : W),
      ρ (GeneralLinear.scalar a) w =
        (c.character (B.diagonalScalarToCenter R a) : ℂ) • w) :
    UnitaryCentralCharacter ρ where
  character := c.character.comp (B.centerToLeviCenter R)
  isOpen_ker := c.isOpen_ker.preimage (B.centerToLeviCenterContinuous R).continuous
  norm_eq_one := fun z => c.norm_eq_one (B.centerToLeviCenter R z)
  acts := by
    intro z w
    have hz := z.property
    simp only [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨a, ha⟩ := hz
    have he : z = GeneralLinear.scalarToCenter a := Subtype.ext ha.symm
    rw [he, MonoidHom.comp_apply, B.centerToLeviCenter_scalar]
    exact hact a w

@[simp]
theorem unitaryCentralCharacterOfLeviScalar_character
    (σ : Representation ℂ (B.Levi R) V)
    (c : UnitaryCentralCharacter σ)
    (ρ : Representation ℂ (GeneralLinear n R) W)
    (hact : ∀ (a : Rˣ) (w : W),
      ρ (GeneralLinear.scalar a) w =
        (c.character (B.diagonalScalarToCenter R a) : ℂ) • w)
    (z : Subgroup.center (GeneralLinear n R)) :
    (B.unitaryCentralCharacterOfLeviScalar R σ c ρ hact).character z =
      c.character (B.centerToLeviCenter R z) := rfl

end Topology

end Langlands.GeneralLinear.BlockShape
