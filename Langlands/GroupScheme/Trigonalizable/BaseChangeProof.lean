import Langlands.GroupScheme.Trigonalizable.BaseChangeStatement
import Langlands.GroupScheme.Trigonalizable.CoordinateLine
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Trigonalizability is preserved by extension of the base field (Milne 16.4) -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Trigonalizable

open AffineLinearEmbedding Unipotent

section Field

variable {k : Type u} [Field k] (C : Grp (CommAlgCat.{u} (CommRingCat.of k))ᵒᵖ)

/-- If the spectrum of an algebra cogroup over a field is trigonalizable, every nonzero
finite-dimensional right-translation stable subspace of its coordinate bialgebra contains a
nonzero semi-invariant. -/
theorem lineStable_of_isTrigonalizable_cogroup
    (h : IsTrigonalizable ((algSpec _).mapGrp.obj C)) : LineStable k C.X.unop := by
  have h' := lineStable_of_isTrigonalizable (Corepresented.cogroupCorepresentation C)
    (IsTrigonalizable.of_iso ((algSpec _).mapGrp.mapIso (Corepresented.cogroupRecoveryIso C)) h)
  rwa [bialgebra_cogroupCorepresentation] at h'

/-- Conversely, if every nonzero finite-dimensional right-translation stable subspace of the
coordinate bialgebra of an algebra cogroup over a field contains a nonzero semi-invariant, its
spectrum is trigonalizable. -/
theorem isTrigonalizable_cogroup_of_lineStable (h : LineStable k C.X.unop) :
    IsTrigonalizable ((algSpec _).mapGrp.obj C) := by
  refine IsTrigonalizable.of_iso
    ((algSpec _).mapGrp.mapIso (Corepresented.cogroupRecoveryIso C)).symm ?_
  apply isTrigonalizable_of_lineStable
  rwa [bialgebra_cogroupCorepresentation]

end Field

/-- Trigonalizability of an affine group scheme over a field is preserved by extension of the
base field. -/
theorem _root_.Langlands.GroupScheme.IsTrigonalizable.baseChange {k K : Type u} [Field k]
    [Field K] [Algebra k K] {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (hH : IsTrigonalizable H) :
    IsTrigonalizable
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let C := AffineCoordinates.coordinateCogroup H
  have h1 : LineStable k C.X.unop := lineStable_of_isTrigonalizable_cogroup C
    (IsTrigonalizable.of_iso (AffineCoordinates.coordinateCogroupIso H) hH)
  have h2 : LineStable K (K ⊗[k] C.X.unop) := LineStable.baseChange K h1
  let C' := ((commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of K)).functor.obj
    (HopfCoordinates.scalarExtension k K C.X.unop)).unop
  have h3 := isTrigonalizable_cogroup_of_lineStable C' h2
  refine IsTrigonalizable.of_iso ?_ h3
  exact (GroupScheme.baseChange _).mapIso (AffineCoordinates.hopfSpecIso H).symm ≪≫
    HopfCoordinates.baseChangeSpecIso k K C.X.unop

end Langlands.GroupScheme.Trigonalizable

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.4: trigonalizability of an affine algebraic group over a field is
preserved by every extension of the base field. -/
theorem trigonalizableBaseChange : TrigonalizableBaseChangeStatement.{u} := by
  intro k K _ _ _ G _ _ hG
  exact hG.baseChange

end Langlands.GroupScheme
