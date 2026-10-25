import Langlands.Representation.Induction.ConjugateParabolic

/-! Conjugation of actual block pairs and consequences of a matrix standardizer. -/
noncomputable section

namespace Langlands.Exponents.ConjugateBlockPair

universe uR
variable {n : ℕ} {R : Type uR} [CommRing R]

/-- Conjugate a concrete block-pair presentation by an ambient matrix. -/
def conjugateBy (P : ConjugateBlockPair n R) (y : GeneralLinear n R) :
    ConjugateBlockPair n R := ⟨P.shape, y * P.conjugator⟩

variable (P : ConjugateBlockPair n R) (y : GeneralLinear n R)

private theorem conj_comp (c : GeneralLinear n R) :
    (MulAut.conj y).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (y * c)).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  change y * (c * x * c⁻¹) * y⁻¹ = (y * c) * x * (y * c)⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- Conjugating the presentation conjugates its actual parabolic subgroup. -/
theorem conjugateBy_parabolic :
    (P.conjugateBy y).parabolic = P.parabolic.map (MulAut.conj y).toMonoidHom := by
  change (P.shape.parabolic R).map (MulAut.conj (y * P.conjugator)).toMonoidHom =
    ((P.shape.parabolic R).map (MulAut.conj P.conjugator).toMonoidHom).map _
  rw [Subgroup.map_map, conj_comp]

/-- The scalar coordinate map of the conjugated presentation is actual conjugation. -/
theorem conjugateBy_scalarMap :
    (P.conjugateBy y).scalarMap = (MulAut.conj y).toMonoidHom.comp P.scalarMap := by
  apply MonoidHom.ext
  intro a
  change (y * P.conjugator) * P.shape.blockScalar R a * (y * P.conjugator)⁻¹ =
    y * (P.conjugator * P.shape.blockScalar R a * P.conjugator⁻¹) * y⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- Conjugating the presentation conjugates its actual split component. -/
theorem conjugateBy_splitComponent :
    (P.conjugateBy y).splitComponent =
      P.splitComponent.map (MulAut.conj y).toMonoidHom := by
  change (P.conjugateBy y).scalarMap.range = P.scalarMap.range.map _
  rw [conjugateBy_scalarMap]
  exact MonoidHom.range_comp _ _

/-- The embedded Levi map is conjugated by the same ambient matrix. -/
theorem conjugateBy_leviEmbedding :
    (P.conjugateBy y).leviEmbedding =
      (MulAut.conj y).toMonoidHom.comp P.leviEmbedding := by
  apply MonoidHom.ext
  intro x
  change (y * P.conjugator) * P.shape.leviEmbedding R x * (y * P.conjugator)⁻¹ =
    y * (P.conjugator * P.shape.leviEmbedding R x * P.conjugator⁻¹) * y⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- Conjugating the presentation conjugates its actual embedded Levi subgroup. -/
theorem conjugateBy_leviSubgroup :
    (P.conjugateBy y).leviSubgroup =
      P.leviSubgroup.map (MulAut.conj y).toMonoidHom := by
  change (P.conjugateBy y).leviEmbedding.range = P.leviEmbedding.range.map _
  rw [conjugateBy_leviEmbedding]
  exact MonoidHom.range_comp _ _

variable (m : P.shape.Levi R) (hm : y * P.conjugator = P.shape.leviEmbedding R m)
include m hm

/-- The matrix standardizer gives exact equality with the standard parabolic. -/
theorem parabolic_map_conj_of_standardizer :
    P.parabolic.map (MulAut.conj y).toMonoidHom = P.shape.parabolic R := by
  rw [← conjugateBy_parabolic]
  change (P.shape.parabolic R).map (MulAut.conj (y * P.conjugator)).toMonoidHom = _
  rw [hm]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((P.shape.parabolic R).le_normalizer (P.shape.leviInParabolic R m).property)

/-- The matrix standardizer fixes the standard block-scalar coordinates pointwise. -/
theorem scalarMap_conj_of_standardizer (a : Fin P.shape.length → Rˣ) :
    y * P.scalarMap a * y⁻¹ = P.shape.blockScalar R a := by
  have hc := P.shape.blockScalarLevi_commute R a m
  have he := congrArg (P.shape.leviEmbedding R) hc
  simp only [map_mul] at he
  change P.shape.blockScalar R a * P.shape.leviEmbedding R m =
    P.shape.leviEmbedding R m * P.shape.blockScalar R a at he
  change y * (P.conjugator * P.shape.blockScalar R a * P.conjugator⁻¹) * y⁻¹ = _
  calc
    _ = (y * P.conjugator) * P.shape.blockScalar R a * (y * P.conjugator)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    _ = P.shape.blockScalar R a := by rw [hm, ← he]; simp only [mul_inv_cancel_right]

/-- The matrix standardizer gives exact equality with the standard split component. -/
theorem splitComponent_map_conj_of_standardizer :
    P.splitComponent.map (MulAut.conj y).toMonoidHom =
      (standard (R := R) P.shape).splitComponent := by
  have h : (MulAut.conj y).toMonoidHom.comp P.scalarMap = P.shape.blockScalar R := by
    apply MonoidHom.ext
    exact scalarMap_conj_of_standardizer P y m hm
  change P.scalarMap.range.map _ = (standard (R := R) P.shape).scalarMap.range
  rw [← MonoidHom.range_comp, h, standard_scalarMap]
  rfl

/-- The matrix standardizer gives exact equality with the standard embedded Levi. -/
theorem leviSubgroup_map_conj_of_standardizer :
    P.leviSubgroup.map (MulAut.conj y).toMonoidHom = P.shape.leviSubgroup R := by
  rw [← conjugateBy_leviSubgroup]
  change ((MulAut.conj (y * P.conjugator)).toMonoidHom.comp
    (P.shape.leviEmbedding R)).range = _
  rw [hm, MonoidHom.range_comp]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((P.shape.leviSubgroup R).le_normalizer ⟨m, rfl⟩)

end Langlands.Exponents.ConjugateBlockPair
