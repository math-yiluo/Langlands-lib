import Langlands.Global.AdelicSpreadSeparatedStatement
import Langlands.Global.AdelicSpreadProductProof
import Langlands.Global.AdelicSpreadClosedImmersionProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Topology.Separation.Hausdorff

/-! # Hausdorff actual adelic points of separated field schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry
open scoped MonoidalCategory

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A closed scheme diagonal and a product homeomorphism make the existing
point topology Hausdorff. -/
private lemma point_t2
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Y : Over (Spec (CommRingCat.of R)))
    (τ : TopologicalSpace (RingPoint R Y A))
    (σ : TopologicalSpace (RingPoint R (Y ⊗ Y) A))
    (hprod : @IsHomeomorph (RingPoint R (Y ⊗ Y) A)
      (RingPoint R Y A × RingPoint R Y A) σ
      (@instTopologicalSpaceProd _ _ τ τ)
      (fun p => (p ≫ fst Y Y, p ≫ snd Y Y)))
    (hdiag : @IsClosedEmbedding (RingPoint R Y A)
      (RingPoint R (Y ⊗ Y) A) τ σ
      (fun p => p ≫ lift (𝟙 Y) (𝟙 Y))) :
    @T2Space (RingPoint R Y A) τ := by
  let : TopologicalSpace (ringTest R A ⟶ Y) := τ
  let : TopologicalSpace (ringTest R A ⟶ Y ⊗ Y) := σ
  have hd := hprod.isClosedEmbedding.comp hdiag
  have heq : (fun p : RingPoint R Y A =>
      ((p ≫ lift (𝟙 Y) (𝟙 Y)) ≫ fst Y Y,
        (p ≫ lift (𝟙 Y) (𝟙 Y)) ≫ snd Y Y)) =
      (fun p => (p, p)) := by
    funext p
    simp
  change IsClosedEmbedding (fun p : RingPoint R Y A =>
    ((p ≫ lift (𝟙 Y) (𝟙 Y)) ≫ fst Y Y,
      (p ≫ lift (𝟙 Y) (𝟙 Y)) ≫ snd Y Y)) at hd
  rw [heq] at hd
  apply t2_iff_isClosed_diagonal.mpr
  have hclosed := hd.isClosed_range
  change IsClosed (Set.range (Function.diag : RingPoint R Y A → _)) at hclosed
  rwa [Set.range_diag] at hclosed

/-- Separation of the field scheme makes its actual diagonal a closed immersion. -/
private lemma diagonal_closed {B : Scheme.{u}} (Y : Over B)
    [IsSeparated Y.hom] :
    IsClosedImmersion (lift (𝟙 Y) (𝟙 Y)).left := by
  change IsClosedImmersion (pullback.diagonal Y.hom)
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The product model and closed field diagonal give function-field
Hausdorffness without separation of the arithmetic model. -/
private lemma curve_spread_separated : CurvePlaceSpreadSeparatedStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S M _ _ Y _ e
  let B := Over.pullback
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
  let c := BinaryFan.mk (fst Y Y) (snd Y Y)
  let eP : curvePlaceModelGenericFiber k F S (M ⨯ M) ≅ Y ⊗ Y :=
    productModelIso B M M e e c (tensorProductIsBinaryProduct Y Y)
  have hfinite := finiteType_overProd M M
  let : LocallyOfFiniteType (M ⨯ M).hom := hfinite.1
  let : QuasiCompact (M ⨯ M).hom := hfinite.2
  have hp := adelicSpreadProduct.1 k F S S S M M (M ⨯ M)
    Y Y e e c eP (tensorProductIsBinaryProduct Y Y)
  let : IsClosedImmersion (lift (𝟙 Y) (𝟙 Y)).left := diagonal_closed Y
  have hd := adelicSpreadClosedImmersion.1 k F S S M (M ⨯ M)
    Y (Y ⊗ Y) e eP (lift (𝟙 Y) (𝟙 Y))
  exact point_t2 F (CurvePlaceAdeleRing k F) Y _ _ hp hd

/-- The same argument for actual full number-field adeles retains all infinite
factors and arbitrary specified finite-type models. -/
private lemma number_spread_separated : NumberFieldSpreadSeparatedStatement.{u} := by
  intro K _ _ S M _ _ Y _ e
  let B := Over.pullback
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
  let c := BinaryFan.mk (fst Y Y) (snd Y Y)
  let eP : numberFieldModelGenericFiber K S (M ⨯ M) ≅ Y ⊗ Y :=
    productModelIso B M M e e c (tensorProductIsBinaryProduct Y Y)
  have hfinite := finiteType_overProd M M
  let : LocallyOfFiniteType (M ⨯ M).hom := hfinite.1
  let : QuasiCompact (M ⨯ M).hom := hfinite.2
  have hp := adelicSpreadProduct.2 K S S S M M (M ⨯ M)
    Y Y e e c eP (tensorProductIsBinaryProduct Y Y)
  let : IsClosedImmersion (lift (𝟙 Y) (𝟙 Y)).left := diagonal_closed Y
  have hd := adelicSpreadClosedImmersion.2 K S S M (M ⨯ M)
    Y (Y ⊗ Y) e eP (lift (𝟙 Y) (𝟙 Y))
  exact point_t2 K (Adeles K) Y _ _ hp hd

/-- Actual adelic points of a separated field scheme, with any specified
finite-type spread topology, are Hausdorff in both arithmetic settings. -/
theorem adelicSpreadSeparated : AdelicSpreadSeparatedStatement.{u} :=
  ⟨curve_spread_separated, number_spread_separated⟩

end Langlands.Global
