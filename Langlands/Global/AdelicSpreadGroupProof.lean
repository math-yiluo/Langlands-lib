import Langlands.Global.AdelicSpreadGroupStatement
import Langlands.Global.AdelicSpreadProductProof
import Langlands.Global.AdelicSpreadFunctorialityProof
import Langlands.Global.AdelicSpreadClosedImmersionProof
import Langlands.Global.AdelicSpreadTopologicalPropertiesProof
import Langlands.GroupScheme.FieldSeparatedProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Topology.Separation.Hausdorff

/-! # The group laws and Hausdorffness of actual adelic group points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidalCategory

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The actual Hom group is topological if the product point comparison is a
homeomorphism and the actual group morphisms induce continuous maps. -/
private lemma pointGroup_topological
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    (τ : TopologicalSpace (RingPoint R G.X A))
    (σ : TopologicalSpace (RingPoint R (G.X ⊗ G.X) A))
    (hprod : @IsHomeomorph (RingPoint R (G.X ⊗ G.X) A)
      (RingPoint R G.X A × RingPoint R G.X A) σ
      (@instTopologicalSpaceProd _ _ τ τ)
      (fun p => (p ≫ fst G.X G.X, p ≫ snd G.X G.X)))
    (hmul : Continuous[σ, τ]
      (fun p : RingPoint R (G.X ⊗ G.X) A => p ≫ μ[G.X]))
    (hinv : Continuous[τ, τ] (fun p : RingPoint R G.X A => p ≫ ι[G.X])) :
    letI : Group (RingPoint R G.X A) :=
      inferInstanceAs (Group (ringTest R A ⟶ G.X))
    letI := τ
    IsTopologicalGroup (RingPoint R G.X A) := by
  let : Group (RingPoint R G.X A) :=
    inferInstanceAs (Group (ringTest R A ⟶ G.X))
  let : TopologicalSpace (ringTest R A ⟶ G.X) := τ
  let : TopologicalSpace (ringTest R A ⟶ G.X ⊗ G.X) := σ
  refine { continuous_mul := ?_, continuous_inv := hinv }
  change Continuous (fun q : RingPoint R G.X A × RingPoint R G.X A =>
    lift q.1 q.2 ≫ μ[G.X])
  apply hmul.comp
  apply hprod.isInducing.continuous_iff.mpr
  convert continuous_id (X := RingPoint R G.X A × RingPoint R G.X A) using 1
  funext q
  exact Prod.ext (lift_fst _ _) (lift_snd _ _)

/-- A closed scheme diagonal and product homeomorphism give the Hausdorff
property for the pre-existing point topology. -/
private lemma pointGroup_t2
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    (τ : TopologicalSpace (RingPoint R G.X A))
    (σ : TopologicalSpace (RingPoint R (G.X ⊗ G.X) A))
    (hprod : @IsHomeomorph (RingPoint R (G.X ⊗ G.X) A)
      (RingPoint R G.X A × RingPoint R G.X A) σ
      (@instTopologicalSpaceProd _ _ τ τ)
      (fun p => (p ≫ fst G.X G.X, p ≫ snd G.X G.X)))
    (hdiag : @IsClosedEmbedding (RingPoint R G.X A)
      (RingPoint R (G.X ⊗ G.X) A) τ σ
      (fun p => p ≫ lift (𝟙 G.X) (𝟙 G.X))) :
    @T2Space (RingPoint R G.X A) τ := by
  let : TopologicalSpace (ringTest R A ⟶ G.X) := τ
  let : TopologicalSpace (ringTest R A ⟶ G.X ⊗ G.X) := σ
  have hd := hprod.isClosedEmbedding.comp hdiag
  have heq : (fun p : RingPoint R G.X A =>
      ((p ≫ lift (𝟙 G.X) (𝟙 G.X)) ≫ fst G.X G.X,
        (p ≫ lift (𝟙 G.X) (𝟙 G.X)) ≫ snd G.X G.X)) =
      (fun p => (p, p)) := by
    funext p
    simp
  change IsClosedEmbedding (fun p : RingPoint R G.X A =>
    ((p ≫ lift (𝟙 G.X) (𝟙 G.X)) ≫ fst G.X G.X,
      (p ≫ lift (𝟙 G.X) (𝟙 G.X)) ≫ snd G.X G.X)) at hd
  rw [heq] at hd
  apply t2_iff_isClosed_diagonal.mpr
  have hclosed := hd.isClosed_range
  change IsClosed (Set.range (Function.diag : RingPoint R G.X A → _)) at hclosed
  rwa [Set.range_diag] at hclosed

/-- Over a field the actual group diagonal is a closed immersion. -/
private lemma group_diagonal_closed
    (F : Type u) [Field F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F))) :
    IsClosedImmersion (lift (𝟙 G.X) (𝟙 G.X)).left := by
  let : IsSeparated G.X.hom := Langlands.GroupScheme.fieldSeparated F G
  change IsClosedImmersion (pullback.diagonal G.X.hom)
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The product model supplies continuity; the closed field diagonal supplies
Hausdorffness without separatedness of the arithmetic model. -/
private lemma curve_spread_group : CurvePlaceSpreadGroupStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S M _ _ G e
  let B := Over.pullback
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
  let c := BinaryFan.mk (fst G.X G.X) (snd G.X G.X)
  let eP : curvePlaceModelGenericFiber k F S (M ⨯ M) ≅ G.X ⊗ G.X :=
    productModelIso B M M e e c (tensorProductIsBinaryProduct G.X G.X)
  have hfinite := finiteType_overProd M M
  let : LocallyOfFiniteType (M ⨯ M).hom := hfinite.1
  let : QuasiCompact (M ⨯ M).hom := hfinite.2
  have hp := adelicSpreadProduct.1 k F S S S M M (M ⨯ M)
    G.X G.X e e c eP (tensorProductIsBinaryProduct G.X G.X)
  have hm := adelicSpreadFunctoriality.1 k F S S (M ⨯ M) M
    (G.X ⊗ G.X) G.X eP e μ[G.X]
  have hi := adelicSpreadFunctoriality.1 k F S S M M G.X G.X e e ι[G.X]
  let : IsClosedImmersion (lift (𝟙 G.X) (𝟙 G.X)).left := group_diagonal_closed F G
  have hd := adelicSpreadClosedImmersion.1 k F S S M (M ⨯ M)
    G.X (G.X ⊗ G.X) e eP (lift (𝟙 G.X) (𝟙 G.X))
  refine ⟨pointGroup_topological F (CurvePlaceAdeleRing k F) G _ _ hp hm hi,
    pointGroup_t2 F (CurvePlaceAdeleRing k F) G _ _ hp hd, ?_⟩
  intro hk
  have ht := adelicSpreadTopologicalProperties.1 k F S M G.X e
  exact ⟨ht.1, ht.2.1⟩

/-- The same argument for full number-field adeles retains all infinite factors. -/
private lemma number_spread_group : NumberFieldSpreadGroupStatement.{u} := by
  intro K _ _ S M _ _ G e
  let B := Over.pullback
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
  let c := BinaryFan.mk (fst G.X G.X) (snd G.X G.X)
  let eP : numberFieldModelGenericFiber K S (M ⨯ M) ≅ G.X ⊗ G.X :=
    productModelIso B M M e e c (tensorProductIsBinaryProduct G.X G.X)
  have hfinite := finiteType_overProd M M
  let : LocallyOfFiniteType (M ⨯ M).hom := hfinite.1
  let : QuasiCompact (M ⨯ M).hom := hfinite.2
  have hp := adelicSpreadProduct.2 K S S S M M (M ⨯ M)
    G.X G.X e e c eP (tensorProductIsBinaryProduct G.X G.X)
  have hm := adelicSpreadFunctoriality.2 K S S (M ⨯ M) M
    (G.X ⊗ G.X) G.X eP e μ[G.X]
  have hi := adelicSpreadFunctoriality.2 K S S M M G.X G.X e e ι[G.X]
  let : IsClosedImmersion (lift (𝟙 G.X) (𝟙 G.X)).left := group_diagonal_closed K G
  have hd := adelicSpreadClosedImmersion.2 K S S M (M ⨯ M)
    G.X (G.X ⊗ G.X) e eP (lift (𝟙 G.X) (𝟙 G.X))
  have ht := adelicSpreadTopologicalProperties.2 K S M G.X e
  exact ⟨pointGroup_topological K (Adeles K) G _ _ hp hm hi,
    pointGroup_t2 K (Adeles K) G _ _ hp hd, ht.1, ht.2.1⟩

/-- Actual adelic points with their specified spread topology form Hausdorff
 topological groups, locally compact and second countable over global fields. -/
theorem adelicSpreadGroup : AdelicSpreadGroupStatement.{u} :=
  ⟨curve_spread_group, number_spread_group⟩

end Langlands.Global
