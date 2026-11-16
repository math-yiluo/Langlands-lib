import Langlands.GroupScheme.Reductive.RankOneRingWeylCalculus
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws
import Langlands.GroupScheme.Torus.ExponentCocharacters

/-! # Rank-one laws in the supplied coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]

/-- The fixed-exponent point is evaluation of the actual cocharacter. -/
theorem cocharPoint_eq_exponentCocharacter (nu : I → ℤ)
    (Z : Over (Spec (CommRingCat.of R))) (d : Γ(Z.left, ⊤)ˣ) :
    cocharPoint nu Z d =
      (Gm.pointsEquiv _ Z).symm d ≫
        (CommGroupScheme.groupHom
          (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu)).hom.hom := by
  apply (splitTorus.pointsEquiv I Z).injective
  simp only [cocharPoint, MulEquiv.apply_symm_apply,
    splitTorus.pointsEquiv_exponentCocharacter]

end LocalSplitCell

namespace RingRootCell.WeylData

open LocalSplitCell

variable {R : Type u} [CommRing R] (D : WeylData R)

/-- The coroot of the Weyl data is the specified coordinate cocharacter
followed by the supplied torus homomorphism. -/
def HasCoordinateCoroot {I : Type u} [Fintype I]
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶ D.T)
    (nu : I → ℤ) : Prop :=
  splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I nu ≫ tau = D.h

/-- If beta is one, the normalized Weyl product is the constant supplied
three-factor product. -/
theorem normalizedWeylPoint_eq_supplied (hbeta : D.cβ = 1)
    (Z : Over (Spec (CommRingCat.of R))) :
    D.normalizedWeylPoint Z = D.G.constantPoint (weylPoint D.xp D.xm) Z := by
  simp only [normalizedWeylPoint, hbeta, pb, map_one,
    constantPoint_weylPoint, CellData.A, CellData.B, rootPoint, gpt, mul_assoc]

/-- A coroot that factors through a coordinate torus has the corresponding
fixed-exponent values on every test. -/
theorem H_eq_cocharPoint {I : Type u} [Fintype I]
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶ D.T)
    (nu : I → ℤ)
    (hnu : D.HasCoordinateCoroot tau nu)
    (Z : Over (Spec (CommRingCat.of R))) (d : Γ(Z.left, ⊤)ˣ) :
    D.H d = cocharPoint nu Z d ≫
      (CommGroupScheme.groupHom tau ≫ D.i).hom.hom := by
  rw [H, CellData.I, tH, ← hnu, comp_groupHom_comp,
    cocharPoint_eq_exponentCocharacter, Grp.comp_hom_hom]
  simp only [Category.assoc]

/-- Beta-one Weyl data give both supplied root conjugations, the square,
and the unit-denominator relation in the fixed coroot coordinates. -/
theorem rankOneLaws_of_beta_eq_one [IsAffine D.G.X.left]
    {I : Type u} [Fintype I]
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶ D.T)
    (nu : I → ℤ)
    (hnu : D.HasCoordinateCoroot tau nu)
    (hbeta : D.cβ = 1) :
    RankOneLaws (CommGroupScheme.groupHom tau ≫ D.i) nu D.xp D.xm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z x
    have h := D.normalizedWeylPoint_conj_A (Z := Z) x
    simpa only [D.normalizedWeylPoint_eq_supplied hbeta, hbeta, pb, map_one,
      neg_mul, one_mul, CellData.A, CellData.B, rootPoint, gpt] using h
  · intro Z x
    have h := D.normalizedWeylPoint_conj_B_beta (Z := Z) x
    simpa only [D.normalizedWeylPoint_eq_supplied hbeta, hbeta, pb, map_one,
      one_mul, CellData.A, CellData.B, rootPoint, gpt] using h
  · intro Z
    have h := D.normalizedWeylPoint_square (Z := Z)
    simpa only [D.normalizedWeylPoint_eq_supplied hbeta,
      D.H_eq_cocharPoint tau nu hnu] using h
  · intro Z x y d hd
    have h := D.relation (Z := Z) x y d hd
    change D.A x * D.B (pb Z D.cβ * y) =
      D.B (pb Z D.cβ * ((↑d⁻¹ : Γ(Z.left, ⊤)) * y)) *
        (D.H d * D.A ((↑d⁻¹ : Γ(Z.left, ⊤)) * x)) at h
    simpa only [hbeta, pb, map_one, one_mul,
      D.H_eq_cocharPoint tau nu hnu, CellData.A, CellData.B,
      rootPoint, gpt, mul_assoc] using h

end RingRootCell.WeylData

end Langlands.GroupScheme
