import Langlands.GroupScheme.Rational.MaximalStandardLeviPointCosetsStatement
import Langlands.GroupScheme.Rational.StandardLeviTransporterCosetsProof

/-! # Maximal standard Levi transporter cosets (Renard VII.1.3) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open StandardMaximalLeviWeyl

/-- V.4.8 gives the maximality and opposite-parabolic assertions on the
Weyl cosets. The transporter comparison carries them to rational points. -/
theorem maximalStandardLeviPointCosets : MaximalStandardLeviPointCosetsStatement.{u} := by
  intro k _ _ _ _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν I conj pointCosets isMaximal
  obtain ⟨e, representative⟩ := standardLeviTransporterCosets k G hG T i hi ν hν I
  have hWeyl := (standardMaximalLeviWeyl k G hG T i hi ν hν I).2
  change (isMaximal ↔ Nat.card (cosets I) = 2) ∧ _ at hWeyl
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr e]
    exact hWeyl.1
  · intro hmax g J hg hJ ζ hζ
    let y : pointCosets := ⟨QuotientGroup.mk g, ⟨g, ⟨J, hJ⟩, rfl⟩⟩
    let x := e.symm y
    obtain ⟨w, ⟨n, hn, _, _⟩, hw⟩ := x.property
    have hx : x.val = QuotientGroup.mk (QuotientGroup.mk n : relativeWeylGroup i) := by
      rw [hn]
      exact hw.symm
    have hcoset : (QuotientGroup.mk (n : RationalPoint k G.X) :
        RationalPoint k G.X ⧸ levi i ν I) = QuotientGroup.mk g :=
      (representative x n hx).symm.trans (congrArg Subtype.val (e.apply_symm_apply y))
    have hLevi : (n : RationalPoint k G.X)⁻¹ * g ∈ levi i ν I :=
      QuotientGroup.eq.mp hcoset
    have hg_mul : g = (n : RationalPoint k G.X) * ((n : RationalPoint k G.X)⁻¹ * g) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hconj (H : Subgroup (RationalPoint k G.X)) (hH : levi i ν I ≤ H) :
        H.map (conj g) = H.map (conj n) := by
      change H.map (MulAut.conj g : RationalPoint k G.X →* RationalPoint k G.X) =
        H.map (MulAut.conj (n : RationalPoint k G.X) : RationalPoint k G.X →* RationalPoint k G.X)
      rw [hg_mul, map_conj_mul, map_conj_eq_self_of_mem (hH hLevi)]
    have hn_out : (QuotientGroup.mk n : relativeWeylGroup i) ∉
        standardRelativeWeylGroup i ν (rootSet i ν I) := by
      intro hmem
      exact hg (hg_mul ▸ (levi i ν I).mul_mem ((mk_mem_iff_mem_levi I n).mp hmem) hLevi)
    rw [hconj _ (levi_le_parabolic i ν I)]
    exact hWeyl.2 hmax n J hn_out ((hconj _ le_rfl).symm.trans hJ) ζ hζ

end Langlands.GroupScheme
