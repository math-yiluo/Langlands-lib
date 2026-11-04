import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.UnipotentPointsNilpotent
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Nilpotence reflected by finite homomorphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The kernel on points over the base field is contained in their abstract centre. -/
def HasCentralBasePointKernel (p : G ⟶ H) : Prop :=
  (((yonedaGrp.map p).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom).ker ≤
    Subgroup.center (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

/-- A finite homomorphism from a smooth connected affine group has central kernel
on base-field points. The full scheme-theoretic kernel need not be central. -/
theorem hasCentralBasePointKernel_of_finiteHom
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (p : G ⟶ H) [IsFinite p.hom.hom.left] : HasCentralBasePointKernel p := by
  intro g hg
  have hgp : g ≫ p.hom.hom = 1 := hg
  have hc : (G.innerIso g).hom = 𝟙 G := by
    apply finiteHom_cancel p
    rw [innerIso_hom_comp, hgp, innerIso_one_hom, Category.comp_id, Category.id_comp]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hx := G.comp_innerIso_hom g (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x
  have hgconst : G.constantPoint g (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = g := by
    change (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k))))) ≫ g = g
    exact Category.id_comp g
  rw [hc, Grp.id_hom_hom, Category.comp_id, hgconst] at hx
  exact (mul_inv_eq_iff_eq_mul.mp hx.symm).symm

/-- Nilpotence of geometric points reflects along any finite homomorphism whose
source is smooth connected affine. No surjectivity or flatness is needed. -/
theorem IsNilpotentGroupScheme.of_finiteHom
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (p : G ⟶ H) [IsFinite p.hom.hom.left] (hH : IsNilpotentGroupScheme H) :
    IsNilpotentGroupScheme G := by
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  have : Smooth (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom e inferInstance
  have : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom e inferInstance
  have : ConnectedSpace (B.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine e
  have : IsFinite (B.map p).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) e p.hom.hom inferInstance
  let : Group.IsNilpotent
      ↑((yonedaGrp.obj (B.obj H)).obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))) := hH
  exact Subgroup.isNilpotent_of_ker_le_center
    (((yonedaGrp.map (B.map p)).app
      (op (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))).hom)
    (hasCentralBasePointKernel_of_finiteHom (B.map p))

/-- Unipotence of an affine target locally of finite type also implies geometric
nilpotence of a smooth connected affine source under a finite homomorphism. -/
theorem isNilpotentGroupScheme_of_finiteHom_of_isUnipotent
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (p : G ⟶ H) [IsFinite p.hom.hom.left] (hH : IsUnipotent H) :
    IsNilpotentGroupScheme G := by
  apply IsNilpotentGroupScheme.of_finiteHom p
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  have : IsAffineHom (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom e inferInstance
  have : LocallyOfFiniteType (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom e inferInstance
  exact isNilpotent_points_of_isUnipotent (hH.baseChange (K := AlgebraicClosure k))
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))

end Langlands.GroupScheme
