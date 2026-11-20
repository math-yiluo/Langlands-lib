import Langlands.GroupScheme.Torus.OrderedProjectorChartBaseChange

/-! # Changing the original affine base of a projector homomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A B : CommRingCat.{u}} (b : Spec A ⟶ Spec R) (c : Spec B ⟶ Spec A)
variable {Λ : Type u} [AddCommGroup Λ]
variable {J n : Type} [Fintype J] [DecidableEq J] [Fintype n] [DecidableEq n]

/-- Compare the direct pullback with the iterated pullback of a given affine group model. -/
def affineModelComparison {G : GroupScheme (Spec R)} {H : GroupScheme (Spec A)}
    (e : (baseChange b).obj G ≅ H) :
    (baseChange (c ≫ b)).obj G ≅ (baseChange c).obj H :=
  (Descent.pullbackComparison b c (c ≫ b) rfl G).symm ≪≫ (baseChange c).mapIso e

private abbrev mapOver : Over.mk (c ≫ b) ⟶ Over.mk b := Over.homMk c rfl

private theorem affineModelComparison_points {G : GroupScheme (Spec R)}
    {H : GroupScheme (Spec A)} (e : (baseChange b).obj G ≅ H) (U : Over (Spec B))
    (x : U ⟶ ((baseChange (c ≫ b)).obj G).X) :
    baseChangePointsEquiv c H U (x ≫ (affineModelComparison b c e).hom.hom.hom) =
      TorusSubgroupModuli.familyPointsEquiv (mapOver b c) U x ≫ e.hom.hom.hom := by
  simp only [affineModelComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Grp.comp_hom_hom, ← Category.assoc]
  rw [baseChangePointsEquiv_comp]
  rfl

private theorem originalPoint {G : GroupScheme (Spec R)} (U : Over (Spec B))
    (x : U ⟶ ((baseChange (c ≫ b)).obj G).X) :
    baseChangePointsEquiv b G ((Over.map c).obj U)
        (TorusSubgroupModuli.familyPointsEquiv (mapOver b c) U x) =
      baseTestComparison (mapOver b c) U ≫ baseChangePointsEquiv (c ≫ b) G U x := by
  apply Over.OverMorphism.ext
  simp only [baseChangePointsEquiv_left, Over.comp_left, baseTestComparison, Over.homMk_left]
  exact TorusSubgroupModuli.familyPointsEquiv_original (mapOver b c) U x

/-- Under the affine-model comparison the pulled-back characters retain their values. -/
theorem sourcePoints_affineModelComparison (U : Over (Spec B))
    (x : U ⟶ ((baseChange (c ≫ b)).obj (Diagonalizable.groupScheme R Λ).toGrp).X)
    (m : Λ) :
    sourcePoints (Over.mk c) Λ U
      (x ≫ (affineModelComparison b c (Diagonalizable.baseChangeIso b Λ)).hom.hom.hom)
      (.ofAdd m) = sourcePoints (Over.mk (c ≫ b)) Λ U x (.ofAdd m) := by
  let G := (Diagonalizable.groupScheme R Λ).toGrp
  let H := (Diagonalizable.groupScheme A Λ).toGrp
  change Diagonalizable.characterPointsEquiv A Λ ((Over.map c).obj U)
    (baseChangePointsEquiv c H U
      (x ≫ (affineModelComparison b c (Diagonalizable.baseChangeIso b Λ)).hom.hom.hom)) _ = _
  rw [affineModelComparison_points]
  have h := Diagonalizable.characterPointsEquiv_baseChangeIso_hom b Λ ((Over.map c).obj U)
    (TorusSubgroupModuli.familyPointsEquiv (mapOver b c) U x)
  refine (congrArg (fun χ : Multiplicative Λ →* Γ(U.left, ⊤)ˣ => χ (.ofAdd m)) h).trans ?_
  change Diagonalizable.characterPointsEquiv R Λ _
    (baseChangePointsEquiv b G ((Over.map c).obj U)
      (TorusSubgroupModuli.familyPointsEquiv (mapOver b c) U x)) (.ofAdd m) = _
  rw [originalPoint b c U x]
  have h := Diagonalizable.characterPointsEquiv_naturality R Λ (baseTestComparison (mapOver b c) U)
    (baseChangePointsEquiv (c ≫ b) G U x) m
  refine h.trans ?_
  apply Units.ext
  change (𝟙 U.left : U.left ⟶ U.left).appTop _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

/-- Under the affine-model comparison the pulled-back matrices retain their entries. -/
theorem targetPoints_affineModelComparison (U : Over (Spec B))
    (x : U ⟶ ((baseChange (c ≫ b)).obj (GeneralLinear.groupScheme n R)).X) :
    targetPoints (Over.mk c) n U
      (x ≫ (affineModelComparison b c (GeneralLinear.baseChangeIso n b)).hom.hom.hom) =
      targetPoints (Over.mk (c ≫ b)) n U x := by
  let G := GeneralLinear.groupScheme n R
  let H := GeneralLinear.groupScheme n A
  change GeneralLinear.pointsEquiv n A ((Over.map c).obj U)
    (baseChangePointsEquiv c H U
      (x ≫ (affineModelComparison b c (GeneralLinear.baseChangeIso n b)).hom.hom.hom)) = _
  rw [affineModelComparison_points]
  have h := GeneralLinear.pointsEquiv_comp_baseChangeIso_hom b (T := (Over.map c).obj U)
    (TorusSubgroupModuli.familyPointsEquiv (mapOver b c) U x)
  refine h.trans ?_
  change GeneralLinear.pointsEquiv n R _
    (baseChangePointsEquiv b G ((Over.map c).obj U)
      (TorusSubgroupModuli.familyPointsEquiv (mapOver b c) U x)) = _
  rw [originalPoint b c U x]
  have h := GeneralLinear.pointsEquiv_naturality (baseTestComparison (mapOver b c) U)
    (baseChangePointsEquiv (c ≫ b) G U x)
  refine h.trans ?_
  apply Units.ext
  ext a d
  change (𝟙 U.left : U.left ⟶ U.left).appTop _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

/-- The projector homomorphism is compatible with changing the original affine base before
pulling the general linear group and the diagonalizable group back to the test scheme. -/
theorem subgroupHom_affineModelComparison (w : J → Λ) (P : Family J n Γ(Spec B, ⊤)) :
    subgroupHom w (Over.mk (c ≫ b)) P ≫
        (affineModelComparison b c (GeneralLinear.baseChangeIso n b)).hom =
      (affineModelComparison b c (Diagonalizable.baseChangeIso b Λ)).hom ≫
        subgroupHom w (Over.mk c) P := by
  refine hom_ext_points fun U x => (targetPoints (Over.mk c) n U).injective ?_
  simp only [Grp.comp_hom_hom, ← Category.assoc, targetPoints_affineModelComparison,
    targetPoints_subgroupHom, sourcePoints_affineModelComparison]

end Langlands.GroupScheme.OrderedProjectorScheme
