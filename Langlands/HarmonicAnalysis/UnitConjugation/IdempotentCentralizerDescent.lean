import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution

/-!
# Centralizers of regular elements in idempotent Levis

For an idempotent `e` in a finite-dimensional algebra over an infinite field, let `M` be its
centralizer. A regular ambient element `X` of `M` acts invertibly on the off-diagonal summand.
Consequently the centralizer of `X` lies in `M`, and the centralizers of `X` in `Mˣ` and `Aˣ`
are isomorphic as groups and homeomorphic for the induced topologies.

This gives the centralizer comparison used in the descent of orbital integrals in
Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (1999),
§1.2, Lemmas 1.5–1.7.
-/

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

universe u v

variable {F : Type u} [Field F] [Infinite F]
variable {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] {e : A}

/-- The commutator with an ambient-regular element of `M` is invertible on the
off-diagonal part. -/
theorem offDiagonalAdjoint_bijective_of_mem_regularSet (he : IsIdempotentElem e)
    (X : Subalgebra.centralizer F ({e} : Set A)) (hX : (X : A) ∈ regularSet F A) :
    Function.Bijective (offDiagonalAdjoint F e X) := by
  obtain ⟨Y, hY, hYoff⟩ := exists_regular_offDiagonal_invertible (F := F) he
  have hRank := lieAlgebraRank_le F (Y : A)
  rw [natTrailingDegree_charpoly_adjointEndomorphism he Y, hYoff,
    (mem_regularSet_iff F Y).mp hY, add_zero] at hRank
  have hXdegree := (mem_regularSet_iff F (X : A)).mp hX
  rw [natTrailingDegree_charpoly_adjointEndomorphism he X] at hXdegree
  have hXrank := lieAlgebraRank_le F X
  have hOff : (offDiagonalAdjoint F e X).charpoly.natTrailingDegree = 0 := by omega
  have hCoeff : (offDiagonalAdjoint F e X).charpoly.constantCoeff ≠ 0 := by
    rw [Polynomial.constantCoeff_apply]
    exact ((Polynomial.natTrailingDegree_eq_zero.mp hOff).resolve_left
      (LinearMap.charpoly_monic _).ne_zero)
  have hInj : Function.Injective (offDiagonalAdjoint F e X) :=
    LinearMap.ker_eq_bot.mp
      (((LinearMap.not_hasEigenvalue_zero_tfae (offDiagonalAdjoint F e X)).out 3 5).mp hCoeff)
  exact ⟨hInj, LinearMap.injective_iff_surjective.mp hInj⟩

/-- Anything commuting with an ambient-regular element of `M` belongs to `M`. -/
theorem centralizer_le_of_mem_regularSet (he : IsIdempotentElem e)
    (X : Subalgebra.centralizer F ({e} : Set A)) (hX : (X : A) ∈ regularSet F A) :
    Subalgebra.centralizer F ({(X : A)} : Set A) ≤ Subalgebra.centralizer F ({e} : Set A) := by
  intro y hy
  have hyX := (mem_centralizer_singleton_iff F).mp hy
  have hXe := (mem_centralizer_singleton_iff F).mp X.property
  have hProj : (X : A) * diagonalProjection F e y = diagonalProjection F e y * (X : A) := by
    rw [← diagonalProjection_mul_left hXe, ← diagonalProjection_mul_right hXe, hyX]
  let yOff : offDiagonal F e := ⟨y - diagonalProjection F e y, by
    rw [mem_offDiagonal_iff, map_sub, diagonalProjection_idem he, sub_self]⟩
  have hZero : offDiagonalAdjoint F e X yOff = 0 := by
    apply Subtype.ext
    rw [offDiagonalAdjoint_apply, Submodule.coe_zero]
    change (X : A) * (y - diagonalProjection F e y) -
      (y - diagonalProjection F e y) * (X : A) = 0
    rw [mul_sub, sub_mul, hyX, hProj, sub_self]
  have hOff : yOff = 0 := (offDiagonalAdjoint_bijective_of_mem_regularSet he X hX).injective
    (hZero.trans (map_zero (offDiagonalAdjoint F e X)).symm)
  have hEq : y = diagonalProjection F e y :=
    sub_eq_zero.mp (congrArg Subtype.val hOff)
  rw [hEq]
  exact (mem_centralizer_singleton_iff F).mpr (commute_diagonalProjection he y)

/-- The topological centralizer of a regular element of an idempotent centralizer is unchanged
by inclusion into the ambient unit group. -/
def conjugationCentralizerEquiv [TopologicalSpace A] (he : IsIdempotentElem e)
    (X : Subalgebra.centralizer F ({e} : Set A)) (hX : (X : A) ∈ regularSet F A) :
    conjugationCentralizer X ≃ₜ* conjugationCentralizer (X : A) := by
  let M := Subalgebra.centralizer F ({e} : Set A)
  let toAmbient (g : conjugationCentralizer X) : conjugationCentralizer (X : A) :=
    ⟨Units.map M.val.toMonoidHom g.val,
      (mem_conjugationCentralizer_iff _ _).mpr
        (congrArg Subtype.val ((mem_conjugationCentralizer_iff _ _).mp g.property))⟩
  let toLevi (g : conjugationCentralizer (X : A)) : conjugationCentralizer X := by
    have hg := (mem_conjugationCentralizer_iff _ _).mp g.property
    have hInv := (mem_conjugationCentralizer_iff _ _).mp
      ((conjugationCentralizer (X : A)).inv_mem g.property)
    let u : Mˣ :=
      ⟨⟨g.val, centralizer_le_of_mem_regularSet he X hX
        ((mem_centralizer_singleton_iff F).mpr hg.symm)⟩,
       ⟨((g.val⁻¹ : Aˣ) : A), centralizer_le_of_mem_regularSet he X hX
         ((mem_centralizer_singleton_iff F).mpr hInv.symm)⟩,
       Subtype.ext g.val.val_inv, Subtype.ext g.val.inv_val⟩
    exact ⟨u, (mem_conjugationCentralizer_iff _ _).mpr (Subtype.ext hg)⟩
  exact
    { toFun := toAmbient
      invFun := toLevi
      left_inv := fun _ => Subtype.ext (Units.ext (Subtype.ext rfl))
      right_inv := fun _ => Subtype.ext (Units.ext rfl)
      map_mul' := fun g h => Subtype.ext (map_mul (Units.map M.val.toMonoidHom) g.val h.val)
      continuous_toFun := ((continuous_subtype_val.units_map M.val.toMonoidHom).comp
        continuous_subtype_val).subtype_mk _
      continuous_invFun := (Units.continuous_iff.mpr
        ⟨(Units.continuous_val.comp continuous_subtype_val).subtype_mk _,
         (Units.continuous_coe_inv.comp continuous_subtype_val).subtype_mk _⟩).subtype_mk _ }

@[simp]
theorem conjugationCentralizerEquiv_apply_val [TopologicalSpace A] (he : IsIdempotentElem e)
    (X : Subalgebra.centralizer F ({e} : Set A)) (hX : (X : A) ∈ regularSet F A)
    (g : conjugationCentralizer X) :
    (conjugationCentralizerEquiv he X hX g).val =
      Units.map (Subalgebra.centralizer F ({e} : Set A)).val.toMonoidHom g.val :=
  rfl

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
