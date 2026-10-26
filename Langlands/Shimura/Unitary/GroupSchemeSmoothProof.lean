import Langlands.Shimura.Unitary.GroupSchemeSmoothStatement
import Langlands.Shimura.Unitary.GaloisCocharacters
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.SimpleRing.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Algebra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinearProduct

/-- The actual finite product of general linear groups and Gm is smooth. -/
theorem smooth_groupScheme (n : ℕ) (I : Type) [Finite I] (R : CommRingCat) :
    Smooth (groupScheme n I R).X.hom := by
  exact GroupScheme.smooth_tensor _ _
    (GroupScheme.smooth_pi _ fun _ => GeneralLinear.smoothStatement (Fin n) R)
    (GroupScheme.smooth_gm (Spec R))

end Langlands.GroupScheme.GeneralLinearProduct

namespace Langlands.Shimura

/-- The actual complex scalar map to the rational base is fpqc. -/
theorem rationalComplexBaseMap_fpqc :
    Surjective rationalComplexBaseMap ∧ Flat rationalComplexBaseMap ∧
      QuasiCompact rationalComplexBaseMap := by
  have h : Flat rationalComplexBaseMap ∧ Surjective rationalComplexBaseMap := by
    apply (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap ℚ ℂ))).2
    change (algebraMap ℚ ℂ).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact ⟨h.2, h.1, inferInstance⟩

namespace CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

include C in
/-- Smoothness of the actual complex Harris group follows from its scheme splitting. -/
theorem complexRationalGroupScheme_smooth : Smooth D.complexRationalGroupScheme.X.hom := by
  apply GroupScheme.smooth_of_over_iso
    ((Grp.forget _).mapIso (D.complexGroupSchemeIso C))
  exact GroupScheme.GeneralLinearProduct.smooth_groupScheme n (E →+* ℝ) (CommRingCat.of ℂ)

/-- Smoothness descends from the actual complex pullback to the rational Harris model. -/
private theorem rationalGroupSchemeSmooth_of_tower : D.RationalGroupSchemeSmooth := by
  intro Φ C
  have h : Smooth (D.rationalBaseChange rationalComplexBaseMap).X.hom :=
    GroupScheme.smooth_of_over_iso
      ((Grp.forget _).mapIso D.complexDirectGroupSchemeIso.symm)
      (D.complexRationalGroupScheme_smooth C)
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := D.rationalGroupScheme.X.hom) (g := rationalComplexBaseMap)
  · exact ⟨⟨rationalComplexBaseMap_fpqc.1, rationalComplexBaseMap_fpqc.2.1⟩,
      rationalComplexBaseMap_fpqc.2.2⟩
  · exact h

omit [IsScalarTower E K A] in
/-- Smoothness of the actual rational Harris model, with exactly the published assumptions. -/
theorem rationalGroupSchemeSmooth : D.RationalGroupSchemeSmooth := by
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
  exact D'.rationalGroupSchemeSmooth_of_tower C'

end CentralSimpleUnitaryData
end Langlands.Shimura
