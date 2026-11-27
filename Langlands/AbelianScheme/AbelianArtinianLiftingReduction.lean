import Langlands.AbelianScheme.LieBaseChange
import Langlands.AbelianScheme.AbelianArtinianLiftingStatement
import Langlands.AbelianScheme.AbelianSmoothArtinianLiftingStatement
import Langlands.AbelianScheme.PointedAbelianArtinianLiftingStatement
import Langlands.AbelianScheme.PointedMorphismRigidityProof

/-! # Abelian-scheme lifts from smooth proper pointed lifts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}}

/-- An isomorphism of underlying pointed schemes over the base between two abelian schemes
gives an isomorphism of abelian schemes. -/
def isoOfPointedIso {A B : AbelianScheme S} (F : A.X ≅ B.X) (hF : η[A.X] ≫ F.hom = η[B.X]) :
    A ≅ B := by
  have hrig : IsMonHom F.hom :=
    pointedMorphismRigidity S A.toGrp B.toGrp A.isAbelian inferInstance inferInstance
      inferInstance F.hom hF
  let G : A.toGrp ≅ B.toGrp := Grp.mkIso F hF hrig.mul_hom
  exact
    { hom := Additive.ofMul G.hom
      inv := Additive.ofMul G.inv
      hom_inv_id := congrArg Additive.ofMul G.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul G.inv_hom_id }

/-- Smooth proper pointed lifts together with the pointed group-law lifting statement give
abelian-scheme lifts across elementary extensions of characteristic-zero local Artinian
rings. -/
theorem abelianArtinianLifting_of_smoothLifting
    (hS : AbelianSmoothArtinianLiftingStatement.{u})
    (hP : PointedAbelianArtinianLiftingStatement.{u}) :
    AbelianArtinianLiftingStatement.{u} := by
  intro R' R _ _ _ _ _ _ _ φ hφ hker B
  obtain ⟨X, p, s, hs, hsm, hpr, e₀, he₀, hη⟩ := hS R' R φ hφ hker B
  obtain ⟨A, e, he, heη⟩ := hP R' R φ hφ hker X p s hs hsm hpr ⟨B, e₀, he₀, hη⟩
  let t := Spec.map (CommRingCat.ofHom φ)
  let m : ((baseChange t).obj A).X.left ⟶ pullback p t :=
    pullback.map A.X.hom t p t e.hom (𝟙 _) (𝟙 _) (by rw [he, Category.comp_id]) (by simp)
  have hm : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  let f₁ : ((baseChange t).obj A).X.left ⟶ A.X.left := pullback.fst A.X.hom t
  have hmf : m ≫ pullback.fst p t = f₁ ≫ e.hom := pullback.lift_fst _ _ _
  have key : η[((baseChange t).obj A).X].left ≫ f₁ = t ≫ η[A.X].left :=
    GroupScheme.identitySection_baseChange_fst t A.toGrp
  have hms : m ≫ pullback.snd p t = pullback.snd A.X.hom t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let F : ((baseChange t).obj A).X ≅ B.X := Over.isoMk (asIso m ≪≫ e₀.symm) (by
    change (m ≫ e₀.inv) ≫ B.X.hom = pullback.snd A.X.hom t
    rw [← he₀, Category.assoc, Iso.inv_hom_id_assoc, hms])
  refine ⟨A, ⟨isoOfPointedIso F ?_⟩⟩
  apply Over.OverMorphism.ext
  change η[((baseChange t).obj A).X].left ≫ (m ≫ e₀.inv) = η[B.X].left
  rw [← cancel_mono e₀.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hmf, ← Category.assoc, key, Category.assoc, heη, hη]
  · simp only [Category.assoc]
    rw [hms, he₀]
    exact (Over.w η[((baseChange t).obj A).X]).trans (Over.w η[B.X]).symm

end Langlands.AbelianScheme
