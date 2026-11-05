import Langlands.GroupScheme.Rational.MatrixEntryBoundedness
import Langlands.GroupScheme.MatrixRepresentation.DirectSum
import Langlands.LinearAlgebra.ValuativeTraceBound
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Spectral bounds on multiplicative rational-point families -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.PointTopology
open ValuativeRel
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

/-- The matrices on a specified set of actual rational points span all matrices. -/
def HasFullRationalMatrixSpanOn (ρ : MatrixRepresentation G (Fin N))
    (B : Set (rationalPoints G)) : Prop :=
  Submodule.span F ((fun g : rationalPoints G =>
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F)) '' B) = ⊤

/-- The characteristic coefficients at one point bound its trace, including
in dimension zero. -/
theorem trace_vle_one_of_charpoly_coeff_vle_one
    (ρ : MatrixRepresentation G (Fin N)) (g : rationalPoints G)
    (h : ∀ d, (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).charpoly.coeff d
      ≤ᵥ (1 : F)) :
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).trace ≤ᵥ (1 : F) := by
  cases isEmpty_or_nonempty (Fin N) with
  | inl h => simp [Matrix.trace, zero_vle]
  | inr hn =>
    rw [Matrix.trace_eq_neg_charpoly_coeff]
    apply (ValuativeRel.valuation F).vle_iff_le.mpr
    simpa only [Valuation.map_neg] using
      (ValuativeRel.valuation F).vle_iff_le.mp (h (Fintype.card (Fin N) - 1))

/-- Coefficient bounds on a multiplicatively closed spanning set bound every
entry on that same set. No condition on the remaining rational points is needed. -/
theorem hasBoundedRationalEntries_of_fullSpanOn
    (ρ : MatrixRepresentation G (Fin N)) (B : Set (rationalPoints G))
    (hmul : ∀ g ∈ B, ∀ h ∈ B, g * h ∈ B)
    (hspan : ρ.HasFullRationalMatrixSpanOn B)
    (hint : ∀ g ∈ B, ∀ d,
      (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).charpoly.coeff d ≤ᵥ (1 : F)) :
    ρ.HasBoundedRationalEntries B := by
  let S : Set (Matrix (Fin N) (Fin N) F) :=
    (fun g : rationalPoints G =>
      (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F)) '' B
  obtain ⟨b, hb, h⟩ := exists_valuative_bound_entries_of_trace_vle_one S S hspan (by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
    simpa only [map_mul, Matrix.GeneralLinearGroup.coe_mul] using
      ρ.trace_vle_one_of_charpoly_coeff_vle_one (x * y) (hint _ (hmul x hx y hy)))
  exact fun i j => ⟨b, hb, fun g hg => h _ ⟨g, hg, rfl⟩ i j⟩

/-- A monoid-indexed spanning family needs coefficient bounds only at its own
values. This is the form used for geometric images of original-field points. -/
theorem hasBoundedRationalEntries_range_of_span
    {I : Type v} [Monoid I] (ρ : MatrixRepresentation G (Fin N))
    (α : I →* rationalPoints G)
    (hspan : Submodule.span F (Set.range fun i =>
      (ρ.rationalMatrix (α i) : Matrix (Fin N) (Fin N) F)) = ⊤)
    (hint : ∀ i d,
      (ρ.rationalMatrix (α i) : Matrix (Fin N) (Fin N) F).charpoly.coeff d ≤ᵥ (1 : F)) :
    ρ.HasBoundedRationalEntries (Set.range α) := by
  apply ρ.hasBoundedRationalEntries_of_fullSpanOn (Set.range α)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨i * j, map_mul α i j⟩
  · simpa only [HasFullRationalMatrixSpanOn, ← Set.range_comp'] using hspan
  · rintro _ ⟨i, rfl⟩ d
    exact hint i d

section DirectSum

variable {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

/-- Entry bounds for the factors give entry bounds for their actual direct sum,
including empty families and empty blocks. -/
theorem hasBoundedRationalEntries_directSum
    (ρ : ∀ i, MatrixRepresentation G (n i)) (B : Set (rationalPoints G))
    (h : ∀ i, (ρ i).HasBoundedRationalEntries B) :
    (directSum ρ).HasBoundedRationalEntries B := by
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    obtain ⟨c, hc, hbound⟩ := h i a b
    refine ⟨c, hc, fun g hg => ?_⟩
    rw [directSum_rationalMatrix_val, Matrix.blockDiagonal'_apply_eq]
    exact hbound g hg
  · refine ⟨1, one_ne_zero, fun g _ => ?_⟩
    rw [directSum_rationalMatrix_val, Matrix.blockDiagonal'_apply_ne _ _ _ hij]
    exact zero_vle (1 : F)

end DirectSum

section Image

variable {n : Type} [Fintype n] [DecidableEq n]

omit [ValuativeRel F] in
/-- Applying the standard representation after a coefficient map recovers its
actual rational matrices. -/
theorem standard_rationalMatrix_comp (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) :
    (standard n (CommRingCat.of F)).rationalMatrix (g ≫ ρ.hom.hom) =
      ρ.rationalMatrix g := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
    (GeneralLinear.pointsEquiv n (CommRingCat.of F) _
      ((g ≫ ρ.hom.hom) ≫ 𝟙 _)) = _
  rw [Category.comp_id]
  rfl

local instance spectralFamilyBoundAffineGL : IsAffine (GeneralLinear.groupScheme n (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme n (CommRingCat.of F)

/-- Entry bounds on an inverse-stable set bound its actual scheme-point image
in the general linear group, whether or not the coefficient map is closed. -/
theorem isAlgebraicallyBounded_image_of_entries
    (ρ : MatrixRepresentation G n) (B : Set (rationalPoints G))
    (hBinv : ∀ g ∈ B, g⁻¹ ∈ B) (h : ρ.HasBoundedRationalEntries B) :
    IsAlgebraicallyBounded F (GeneralLinear.groupScheme n (CommRingCat.of F)).X
      ((fun g => g ≫ ρ.hom.hom) '' B) := by
  let σ := standard n (CommRingCat.of F)
  have hσ : IsClosedSubgroup σ := by
    show IsClosedImmersion (𝟙 (GeneralLinear.groupScheme n (CommRingCat.of F)).X.left)
    infer_instance
  apply σ.isAlgebraicallyBounded_of_entries hσ
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, hBinv g hg, GrpObj.inv_comp g ρ.hom.hom⟩
  · intro i j
    obtain ⟨b, hb, hbound⟩ := h i j
    refine ⟨b, hb, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    rw [standard_rationalMatrix_comp]
    exact hbound g hg

end Image

end Langlands.GroupScheme.MatrixRepresentation
