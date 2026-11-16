import Langlands.GroupScheme.Reductive.RankOneRingWeylCalculus

/-! # Uniqueness of the rank-one Weyl normalization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RingRootCell.WeylData

variable {R : Type u} [CommRing R] (D : WeylData R)
  {Z : Over (Spec (CommRingCat.of R))}

/-- The Weyl product in the supplied, unscaled root coordinates. -/
def unscaledWeylPoint (Z : Over (Spec (CommRingCat.of R))) : Z ⟶ D.G.X :=
  D.B (-1) * (D.A 1 * D.B (-1))

/-- The quotient of the unscaled and normalized Weyl products is in the
open cell, with explicit two root coordinates. -/
theorem unscaledWeylPoint_mul_normalized_inv [IsAffine D.G.X.left] :
    D.unscaledWeylPoint Z * (D.normalizedWeylPoint Z)⁻¹ =
      D.B (pb Z D.cβ - 1) *
        D.A ((↑(D.unitβ.map (toBase Z).left.appTop.hom).unit⁻¹ :
          Γ(Z.left, ⊤)) - 1) := by
  let β := pb Z D.cβ
  let b := (D.unitβ.map (toBase Z).left.appTop.hom).unit
  have hb : (b : Γ(Z.left, ⊤)) = β := IsUnit.unit_spec _
  have hcoord : β * (1 - (↑b⁻¹ : Γ(Z.left, ⊤))) = β - 1 := by
    rw [← hb, mul_sub, mul_one, Units.mul_inv]
  have hconj := D.normalizedWeylPoint_conj_B_beta (Z := Z)
    (1 - (↑b⁻¹ : Γ(Z.left, ⊤)))
  rw [hcoord] at hconj
  have hfactor : D.unscaledWeylPoint Z =
      D.B (β - 1) * (D.normalizedWeylPoint Z * D.B (β - 1)) := by
    have h₁ : β - 1 + -β = -1 := by ring
    have h₂ : -β + (β - 1) = -1 := by ring
    calc
      _ = D.B (β - 1 + -β) * (D.A 1 * D.B (-β + (β - 1))) := by
        rw [h₁, h₂]
        rfl
      _ = _ := by
        rw [CellData.B_add, CellData.B_add]
        simp only [normalizedWeylPoint, β, mul_assoc]
  rw [hfactor, mul_assoc, hconj]
  congr 1
  congr 1
  ring

/-- If the unscaled Weyl product already gives the prescribed reflection
and the torus self-centralizes, the supplied cell coefficient beta is one. -/
theorem cβ_eq_one_of_unscaled_normalizes [IsAffine D.G.X.left]
    (hself : torusCentralizer D.i = SubgroupFunctor.range D.i)
    (hn : IsNormalizingPoint D.i (D.unscaledWeylPoint (base R))
      (reflectionIso D.α D.h D.hh)) :
    D.cβ = 1 := by
  have hc : D.unscaledWeylPoint (base R) *
      (D.normalizedWeylPoint (base R))⁻¹ ∈ centralizerPoints D.i := by
    change IsNormalizingPoint D.i _ (Iso.refl D.T)
    simpa only [Iso.symm_self_id] using
      hn.mul D.normalizedWeylPoint_isNormalizing.inv
  have hr := centralizerPoints_le_torusCentralizer D.i hc
  rw [hself] at hr
  change ∃ z : base R ⟶ D.T.X, z ≫ D.i.hom.hom =
    D.unscaledWeylPoint (base R) * (D.normalizedWeylPoint (base R))⁻¹ at hr
  obtain ⟨z, hz⟩ := hr
  have hcell :
      D.cellPt (pb (base R) D.cβ - 1) 1
        ((↑(D.unitβ.map (toBase (base R)).left.appTop.hom).unit⁻¹ :
          Γ((base R).left, ⊤)) - 1) =
      D.cellPt 0 z 0 := by
    rw [CellData.cellPt, CellData.I_one, one_mul,
      ← unscaledWeylPoint_mul_normalized_inv, ← CellData.I_eq_cellPt]
    exact hz.symm
  have hβ := (D.cellPt_inj hcell).1
  have hpb : pb (base R) D.cβ = D.cβ := by
    simp [pb, toBase]
  rw [hpb] at hβ
  exact sub_eq_zero.mp hβ

end Langlands.GroupScheme.RingRootCell.WeylData
