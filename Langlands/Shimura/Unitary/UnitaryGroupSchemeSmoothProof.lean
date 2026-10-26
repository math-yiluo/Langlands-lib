import Langlands.Shimura.Unitary.UnitaryGroupSchemeSmoothStatement
import Langlands.Shimura.Unitary.ComplexUnitaryComparison
import Langlands.Shimura.Unitary.GroupSchemeSmoothProof

noncomputable section
open CategoryTheory AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- Smoothness of the actual rational unitary scheme descends from its split complex form. -/
private theorem rationalUnitaryGroupSchemeSmooth_of_tower : D.RationalUnitaryGroupSchemeSmooth := by
  intro Φ C
  have hsplit : Smooth D.complexSplitUnitaryGroupScheme.X.hom :=
    GroupScheme.smooth_pi _ fun _ =>
      GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of ℂ)
  have h : Smooth (D.rationalUnitaryBaseChange rationalComplexBaseMap).X.hom :=
    GroupScheme.smooth_of_over_iso
      ((Grp.forget _).mapIso (D.directComplexUnitaryGroupSchemeIso C)) hsplit
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := D.rationalUnitaryGroupScheme.X.hom) (g := rationalComplexBaseMap)
  · exact ⟨⟨rationalComplexBaseMap_fpqc.1, rationalComplexBaseMap_fpqc.2.1⟩,
      rationalComplexBaseMap_fpqc.2.2⟩
  · exact h

omit [IsScalarTower E K A] in
/-- Smoothness of the actual rational unitary scheme, with exactly the published assumptions. -/
theorem rationalUnitaryGroupSchemeSmooth : D.RationalUnitaryGroupSchemeSmooth := by
  intro Φ C
  classical
  let : Algebra.IsCentral K A := D.central
  let : IsSimpleRing A := D.simple
  have hdegree : Module.finrank ℚ K = Module.finrank ℚ E * 2 := by
    rw [← Module.finrank_mul_finrank ℚ E K, IsQuadraticExtension.finrank_eq_two E K]
  have hlift (x : E) : ∃ y : K, algebraMap K A y = algebraMap E A x := by
    apply (Algebra.mem_bot (R := K)).mp
    apply Algebra.IsCentral.out
    exact Subalgebra.mem_center_iff.mpr (fun a => (Algebra.commutes x a).symm)
  choose f hf using hlift
  let e : E →+* K :=
    { toFun := f
      map_one' := (algebraMap K A).injective (by simp only [hf, map_one])
      map_mul' := fun x y => (algebraMap K A).injective (by simp only [map_mul, hf])
      map_zero' := (algebraMap K A).injective (by simp only [hf, map_zero])
      map_add' := fun x y => (algebraMap K A).injective (by simp only [map_add, hf]) }
  let involution := D.involution
  have onCenter := D.onCenter
  have rank_gt_one := D.rank_gt_one
  have central := D.central
  have simple := D.simple
  have finite := D.finite
  have dimension := D.dimension
  have chart_rank := C.rank_gt_one
  let distinguished := C.distinguished
  let equiv := C.equiv
  have compatible := C.compatible
  have center := C.center
  let : Algebra E K := e.toAlgebra
  let : IsScalarTower E K A := IsScalarTower.of_algebraMap_eq (fun x => (hf x).symm)
  let : IsQuadraticExtension E K :=
    { finrank_eq_two' := Nat.eq_of_mul_eq_mul_left
        (show 0 < Module.finrank ℚ E from Module.finrank_pos)
        ((Module.finrank_mul_finrank ℚ E K).trans hdegree) }
  let D' : CentralSimpleUnitaryData E K A n :=
    { involution := involution
      onCenter := onCenter
      rank_gt_one := rank_gt_one
      central := central
      simple := simple
      finite := finite
      dimension := dimension }
  let C' : HarrisSignatureCharts D'.toSecondKindInvolution n Φ :=
    { rank_gt_one := chart_rank
      distinguished := distinguished
      equiv := equiv
      compatible := compatible
      center := center }
  exact D'.rationalUnitaryGroupSchemeSmooth_of_tower C'


end Langlands.Shimura.CentralSimpleUnitaryData
