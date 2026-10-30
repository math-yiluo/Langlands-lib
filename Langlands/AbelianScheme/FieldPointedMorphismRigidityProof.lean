import Langlands.AbelianScheme.FieldPointedMorphismRigidity
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidityProof
import Langlands.GroupScheme.FieldSeparatedProof
import Mathlib.AlgebraicGeometry.Group.Abelian

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.AbelianScheme

private theorem isMonHom_of_defect_eq_one {S : Scheme.{u}}
    (A H : GroupScheme S) (f : A.X ⟶ H.X) (hf : η[A.X] ≫ f = η[H.X])
    (hd : (μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f)) = 1) :
    IsMonHom f := by
  refine ⟨hf, ?_⟩
  have hm := div_eq_one.mp hd
  rw [CategoryTheory.Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp] at hm
  exact hm

private theorem defect_left_axis {S : Scheme.{u}}
    (A H : GroupScheme S) (f : A.X ⟶ H.X) (hf : η[A.X] ≫ f = η[H.X]) :
    (η[A.X] ▷ A.X) ≫
      ((μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f))) = 1 := by
  simp only [GrpObj.comp_div, MonObj.comp_mul, MonObj.one_mul_assoc,
    whiskerRight_fst_assoc, whiskerRight_snd_assoc, hf, leftUnitor_hom]
  simp only [MonObj.one_eq_one, MonObj.comp_one, one_mul, div_self']

private theorem defect_right_axis {S : Scheme.{u}}
    (A H : GroupScheme S) (f : A.X ⟶ H.X) (hf : η[A.X] ≫ f = η[H.X]) :
    (A.X ◁ η[A.X]) ≫
      ((μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f))) = 1 := by
  simp only [GrpObj.comp_div, MonObj.comp_mul, MonObj.mul_one_assoc,
    whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hf, rightUnitor_hom]
  simp only [MonObj.one_eq_one, MonObj.comp_one, mul_one, div_self']

private theorem map_defect_eq_one {S T : Scheme.{u}} (b : T ⟶ S)
    (A H : GroupScheme S) (f : A.X ⟶ H.X)
    [IsMonHom ((Over.pullback b).map f)] :
    (Over.pullback b).map
      ((μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f))) = 1 := by
  simp only [div_eq_mul_inv, MonObj.mul_eq_mul, Functor.map_comp, Functor.map_mul,
    Functor.map_inv', MonObj.mul_comp, mul_inv_cancel]

set_option backward.defeqAttrib.useBackward true in
/-- Every unit-preserving morphism in the published all-field rigidity statement
preserves multiplication. -/
theorem fieldPointedMorphismRigidity : FieldPointedMorphismRigidity.{u} := by
  intro K _ A H hA hHfp hHqc hHqs f hf
  let : Smooth A.X.hom := hA.1
  let : IsProper A.X.hom := hA.2.1
  let : GeometricallyConnected A.X.hom := hA.2.2
  let : LocallyOfFinitePresentation H.X.hom := hHfp
  let : QuasiCompact H.X.hom := hHqc
  let : QuasiSeparated H.X.hom := hHqs
  have : GeometricallyIntegral A.X.hom :=
    smoothGeometricIntegrality K A.X.left A.X.hom inferInstance inferInstance
  let b := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback b
  let A' := F.mapGrp.obj A
  let H' := F.mapGrp.obj H
  have : IsProper A'.X.hom := by
    change IsProper (Limits.pullback.snd A.X.hom b)
    infer_instance
  have : IsIntegral (A'.X ⊗ A'.X).left := by
    dsimp [A', F]
    infer_instance
  have : IsSeparated H'.X.hom :=
    Langlands.GroupScheme.fieldSeparated (AlgebraicClosure K) H'
  have : LocallyOfFiniteType H'.X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd H.X.hom b)
    infer_instance
  have hf' : η[A'.X] ≫ F.map f = η[H'.X] := by
    change η[F.obj A.X] ≫ F.map f = η[F.obj H.X]
    simp only [Functor.obj.η_def, Category.assoc, ← Functor.map_comp, hf]
  have : IsMonHom (F.map f) := by
    apply isMonHom_of_defect_eq_one A' H' (F.map f) hf'
    exact algebraicallyClosedTwoAxisRigidity (AlgebraicClosure K) A'.X H'.X
      inferInstance inferInstance inferInstance inferInstance η[A'.X] η[H'.X] _
      (defect_left_axis A' H' (F.map f) hf')
      (defect_right_axis A' H' (F.map f) hf')
  apply isMonHom_of_defect_eq_one A H f hf
  apply F.map_injective
  rw [Functor.map_one]
  exact map_defect_eq_one b A H f

end Langlands.AbelianScheme
