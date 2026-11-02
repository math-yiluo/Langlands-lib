import Langlands.GroupScheme.AffineLinearEmbeddingStatement
import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.AffineLinearEmbedding.Comodule
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate

/-! # Proof of the closed linear embedding theorem for affine algebraic groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineLinearEmbedding

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) {B : CommAlgCat.{u} R}
  (j : (algSpec R).obj (op B) ≅ G.X)

/-- An identification of the underlying scheme of `G` with `Spec B` corepresents the
algebra-point functor of `G` by `B`. -/
def corepresentableBy : (G.affinePointFunctor ⋙ forget GrpCat).CorepresentableBy B where
  homEquiv {A} := show (B ⟶ A) ≃ ((algSpec R).obj (op A) ⟶ G.X) from
    { toFun := fun f => (algSpec R).map f.op ≫ j.hom
      invFun := fun x => (algSpec.fullyFaithful.preimage (x ≫ j.inv)).unop
      left_inv := fun f => by simp
      right_inv := fun x => by simp }
  homEquiv_comp {A A'} f g := by
    change (algSpec R).map (g ≫ f).op ≫ j.hom = (algSpec R).map f.op ≫ (algSpec R).map g.op ≫ j.hom
    rw [op_comp, Functor.map_comp, Category.assoc]

/-- The affine group scheme built from the corepresentation. -/
abbrev model : GroupScheme (Spec R) :=
  Corepresented.groupScheme G.affinePointFunctor (corepresentableBy G j)

/-- Points of the model, transported along `j`, are computed through the relative adjunction. -/
theorem comp_hom (T : Over (Spec R)) (x : T ⟶ (model G j).X) :
    x ≫ j.hom = (algΓAlgSpecAdjunction R).unit.app T ≫
      (Corepresented.pointsEquiv G.affinePointFunctor (corepresentableBy G j) T x :
        (algSpec R).obj ((algΓ R).obj T) ⟶ G.X) := by
  rw [Corepresented.pointsEquiv_apply]
  change x ≫ j.hom = _ ≫ (algSpec R).map
    (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x) ≫ j.hom
  rw [← Category.assoc, ← Adjunction.homEquiv_unit]
  exact (congrArg (fun y => y ≫ j.hom)
    (((algΓAlgSpecAdjunction R).homEquiv T (op B)).apply_symm_apply x)).symm

/-- Composition with `j` is a group isomorphism on points over every test scheme. -/
def pointsMulEquiv (T : Over (Spec R)) : (T ⟶ (model G j).X) ≃* (T ⟶ G.X) where
  toFun x := x ≫ j.hom
  invFun y := y ≫ j.inv
  left_inv x :=
    (Category.assoc _ _ _).trans ((congrArg (fun f => x ≫ f) j.hom_inv_id).trans
      (Category.comp_id x))
  right_inv y := by simp
  map_mul' x y := by
    simp only [comp_hom, map_mul]
    exact MonObj.comp_mul _ _ _

/-- The model is isomorphic to `G` as a group scheme. -/
def modelIso : model G j ≅ G :=
  (yonedaGrpFullyFaithful (C := Over (Spec R))).preimageIso
    (NatIso.ofComponents (fun T => (pointsMulEquiv G j T.unop).toGrpIso)
      (fun f => by
        ext x
        change (f.unop ≫ x) ≫ j.hom = f.unop ≫ x ≫ j.hom
        exact Category.assoc _ _ _))

end Langlands.GroupScheme.AffineLinearEmbedding

namespace Langlands.GroupScheme

open AffineLinearEmbedding

/-- Milne, *Algebraic Groups* (2017), Theorem 4.9 and Corollary 4.10: every affine group
scheme of finite type over a field admits a closed linear embedding. -/
theorem affineLinearEmbeddingStatement : AffineLinearEmbeddingStatement.{u} := by
  intro k _ G hAff hLFT
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨B⟩, ⟨j⟩⟩ := (essImage_algSpec (G := G.X)).mpr this
  -- The coordinate algebra is of finite type.
  have hft : Algebra.FiniteType (CommRingCat.of k) B := by
    have h : LocallyOfFiniteType ((algSpec (CommRingCat.of k)).obj (op B)).hom := by
      have : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
      rw [← Over.w j.hom]
      exact MorphismProperty.comp_mem _ _ _ inferInstance hLFT
    exact RingHom.finiteType_algebraMap.mp
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp h)
  obtain ⟨s, hs⟩ := hft.out
  -- The coordinate bialgebra and its matrix coefficients.
  let e := corepresentableBy G j
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  let := (bialgebra e).toCoalgebra
  obtain ⟨N, M, hcomul, hcounit, hspan⟩ :=
    exists_matrix_coefficients (K := CommRingCat.of k) (B := B) s
  have hgen : Algebra.adjoin (CommRingCat.of k)
      (Set.range fun p : Fin N × Fin N => M p.1 p.2) = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact Algebra.adjoin_le fun b hb => Algebra.span_le_adjoin _ _ (hspan hb)
  refine ⟨N, (modelIso G j).inv ≫ toGLHom e M hcomul hcounit, ?_⟩
  have hmodel := isClosedSubgroup_toGLHom e M hcomul hcounit hgen
  have : IsIso (modelIso G j).inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (modelIso G j).inv.hom.hom))
  have : IsClosedImmersion (toGLHom e M hcomul hcounit).hom.hom.left := hmodel
  change IsClosedImmersion
    ((modelIso G j).inv.hom.hom.left ≫ (toGLHom e M hcomul hcounit).hom.hom.left)
  infer_instance

end Langlands.GroupScheme
