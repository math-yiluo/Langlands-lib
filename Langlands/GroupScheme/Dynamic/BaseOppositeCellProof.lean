import Langlands.GroupScheme.Dynamic.BaseOppositeCellStatement
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.SmoothProducts
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion

/-! # The opposite dynamic open cell over an arbitrary base scheme: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace DynamicBaseOppositeCell

variable {S T : Scheme.{u}} {G U P : GroupScheme S}

/-- Base change of the ordered multiplication is multiplication after the canonical
comparison of the two source products. -/
theorem baseChange_cellMultiplication (b : T ⟶ S) (iU : U ⟶ G) (iP : P ⟶ G) :
    (Over.pullback b).map (SubgroupFunctor.cellMultiplication iU iP) =
      CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X ≫
        SubgroupFunctor.cellMultiplication (S := T)
          (G := (GroupScheme.baseChange b).obj G)
          (U := (GroupScheme.baseChange b).obj U)
          (P := (GroupScheme.baseChange b).obj P)
          ((GroupScheme.baseChange b).map iU) ((GroupScheme.baseChange b).map iP) := by
  change (Over.pullback b).map (SubgroupFunctor.cellMultiplication iU iP) =
    CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X ≫
      ((fst ((Over.pullback b).obj U.X) ((Over.pullback b).obj P.X) ≫
          (Over.pullback b).map iU.hom.hom) *
        (snd ((Over.pullback b).obj U.X) ((Over.pullback b).obj P.X) ≫
          (Over.pullback b).map iP.hom.hom))
  simp only [SubgroupFunctor.cellMultiplication, Functor.map_mul, Functor.map_comp,
    MonObj.comp_mul, CartesianMonoidalCategory.prodComparison_fst_assoc,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

/-- Smoothness over arbitrary bases is detected after base change to affine schemes. -/
theorem smooth_of_affine_baseChange {H : GroupScheme S}
    (h : ∀ (R : Type u) [CommRing R] (b : Spec (CommRingCat.of R) ⟶ S),
      Smooth ((GroupScheme.baseChange b).obj H).X.hom) :
    Smooth H.X.hom :=
  IsZariskiLocalAtTarget.of_openCover (P := @Smooth) S.affineOpenCover.openCover fun i =>
    h (S.affineOpenCover.X i) (S.affineOpenCover.f i)

/-- Actual dynamic parabolic and unipotent representatives of a smooth affine group are
smooth over an arbitrary base scheme. -/
theorem smooth_representatives [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (H : GroupScheme S) (j : H ⟶ G) :
    ((Dynamic.parabolic χ).IsRepresentedBy j → Smooth H.X.hom) ∧
    ((Dynamic.unipotent χ).IsRepresentedBy j → Smooth H.X.hom) := by
  have hs (R : Type u) [CommRing R] (b : Spec (CommRingCat.of R) ⟶ S) :
      Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have ha (R : Type u) [CommRing R] (b : Spec (CommRingCat.of R) ⟶ S) :
      IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom b ‹_›
  constructor
  · intro hj
    refine smooth_of_affine_baseChange fun R _ b => ?_
    have := hs R b
    have := ha R b
    have hjR := hj.baseChange b
    rw [← Dynamic.parabolic_baseChange] at hjR
    exact (dynamicSmooth_ring R _ (Dynamic.baseChangeCocharacter b χ) _ _).1 hjR
  · intro hj
    refine smooth_of_affine_baseChange fun R _ b => ?_
    have := hs R b
    have := ha R b
    have hjR := hj.baseChange b
    rw [← Dynamic.unipotent_baseChange] at hjR
    exact (dynamicSmooth_ring R _ (Dynamic.baseChangeCocharacter b χ) _ _).2.2 hjR

/-- The base change of the ordered multiplication along every field-valued point is an open
immersion, by the published field opposite cell. -/
theorem isOpenImmersion_field_baseChange [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S) :
    IsOpenImmersion ((Over.pullback b).map
      (SubgroupFunctor.cellMultiplication iU iP)).left := by
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom b ‹_›
  have hUb := hU.baseChange b
  rw [← Dynamic.unipotent_baseChange, Dynamic.baseChangeCocharacter_powerHom] at hUb
  have hPb := hP.baseChange b
  rw [← Dynamic.parabolic_baseChange] at hPb
  have hopen : IsOpenImmersion
      (SubgroupFunctor.cellMultiplication (S := Spec (CommRingCat.of K))
        (G := (GroupScheme.baseChange b).obj G)
        (U := (GroupScheme.baseChange b).obj U)
        (P := (GroupScheme.baseChange b).obj P)
        ((GroupScheme.baseChange b).map iU) ((GroupScheme.baseChange b).map iP)).left :=
    oppositeCellStatement K _ (Dynamic.baseChangeCocharacter b χ) _ _ _ _ hUb hPb
  rw [baseChange_cellMultiplication, Over.comp_left]
  have : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X).left := by
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map
      (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X))
    infer_instance
  infer_instance

end DynamicBaseOppositeCell

open DynamicBaseOppositeCell in
/-- The opposite dynamic multiplication is an open immersion for any smooth affine group
scheme over any base scheme. -/
theorem dynamicBaseOppositeCell : DynamicBaseOppositeCellStatement.{u} := by
  intro S G _ _ χ U P iU iP hU hP
  have hUs : Smooth U.X.hom :=
    (smooth_representatives
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ) U iU).2 hU
  have hPs : Smooth P.X.hom := (smooth_representatives χ P iP).1 hP
  have : Smooth (U.X ⊗ P.X).hom := smooth_tensor U.X P.X hUs hPs
  apply Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise
  intro s
  exact isOpenImmersion_field_baseChange χ iU iP hU hP
    (S.residueField s) (S.fromSpecResidueField s)

end Langlands.GroupScheme
