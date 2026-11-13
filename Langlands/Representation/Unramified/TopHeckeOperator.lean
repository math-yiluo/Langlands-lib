import Langlands.Representation.Unramified.PairedHeckeScalars

/-! # The top standard Hecke operator

The `(r + 1)`-st standard diagonal of `GL_(r+1)(F)` is the scalar matrix `ϖ · 1`, which is
central, so its double coset under `K = GL_(r+1)(O_F)` is the single left coset `ϖ K`. On a
`K`-fixed vector the top standard Hecke operator is therefore translation by `ϖ · 1`, and its
standard Hecke scalar is the top elementary coefficient, the normalizing exponent being zero.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence MinusculeCosets

universe uF uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The top standard diagonal is the scalar matrix of the uniformizer. -/
theorem standardDiagonal_last :
    standardDiagonal F r (Fin.last (r + 1)) =
      Matrix.GeneralLinearGroup.scalar (Fin (r + 1))
        F.canonicalTopologicalData.uniformizerUnit := by
  apply Units.ext
  rw [standardDiagonal_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  congr 1
  funext j
  exact ite_eq_left_iff.mpr fun h => absurd (by rw [Fin.val_last]; exact j.isLt) h

/-- The top standard diagonal is central. -/
theorem standardDiagonal_last_commute (g : GeneralLinear (r + 1) F.Carrier) :
    Commute (standardDiagonal F r (Fin.last (r + 1))) g := by
  rw [standardDiagonal_last]
  change _ * _ = _ * _
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact Matrix.scalar_comm _ (Commute.all _) g.val

/-- The index set of the top double coset has exactly one element. -/
instance cosetIndex_last_subsingleton (Λ : Type*) (m : ℕ) :
    Subsingleton (CosetIndex Λ m m) := by
  constructor
  rintro ⟨⟨S, hS⟩, w⟩ ⟨⟨S', hS'⟩, w'⟩
  obtain rfl : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS, Fintype.card_fin])
  obtain rfl : S' = Finset.univ := Finset.eq_univ_of_card S' (by rw [hS', Fintype.card_fin])
  have hw : w = w' := funext fun q => (q.2.2.1 (Finset.mem_univ _)).elim
  subst hw
  rfl

/-- The unique element of the index set of the top double coset. -/
def cosetIndexLast (Λ : Type*) (m : ℕ) : CosetIndex Λ m m :=
  ⟨⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]⟩,
    fun q => (q.2.2.1 (Finset.mem_univ _)).elim⟩

/-- On a `GL_(r+1)(O_F)`-fixed vector, the top standard Hecke operator is translation by the
scalar matrix of the uniformizer. -/
theorem standardHecke_cornerAction_last
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsSmooth ρ)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) :
    (PairedHecke.corner F ρ hρ (standardHeckeElement F r (Fin.last (r + 1))) a : V) =
      ρ (standardDiagonal F r (Fin.last (r + 1))) a := by
  have : Subsingleton (CosetIndex F.canonicalTopologicalData.ResidueField (r + 1)
      (Fin.last (r + 1)).val) := cosetIndex_last_subsingleton _ _
  refine (standardHecke_cornerAction_eq_sum F ρ hρ (Fin.last (r + 1)) a).trans ?_
  refine (Fintype.sum_subsingleton (fun α => ρ (labelledRep F.canonicalTopologicalData.uniformizerUnit
    (residueLift F) α) (a : V))
    (cosetIndexLast F.canonicalTopologicalData.ResidueField (r + 1))).trans ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ :=
    labelledRep_mem_doubleCoset (ϖ := F.canonicalTopologicalData.uniformizerUnit)
      (residueLift_mem F) (card_initialSegment r (Fin.last (r + 1)))
      (cosetIndexLast F.canonicalTopologicalData.ResidueField (r + 1))
  rw [hx, ← standardDiagonal_eq_subsetTorus, map_mul, map_mul]
  have h₂ : ρ k₂ (a : V) = a := a.property ⟨k₂, hk₂⟩
  have h₁ : ρ k₁ (a : V) = a := a.property ⟨k₁, hk₁⟩
  change ρ k₁ (ρ (standardDiagonal F r (Fin.last (r + 1))) (ρ k₂ (a : V))) = _
  rw [h₂, ← Module.End.mul_apply, ← map_mul,
    ← (standardDiagonal_last_commute F k₁).eq, map_mul, Module.End.mul_apply, h₁]

/-- The top standard Hecke scalar is the top elementary coefficient. -/
theorem standardHeckeScalar_last (s : Eigenvalues (r + 1)) :
    standardHeckeScalar F s (Fin.last (r + 1)) = elementaryCoefficient s (r + 1) := by
  rw [standardHeckeScalar, Fin.val_last, Nat.sub_self, Nat.mul_zero, pow_zero, one_mul]

end Langlands.Unramified
