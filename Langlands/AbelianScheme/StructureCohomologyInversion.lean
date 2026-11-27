import Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonProof

/-! # Inversion in low-degree structure-sheaf cohomology -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology (structureCohomology)

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Inversion acts by minus one on degree-one structure-sheaf cohomology over a field. -/
theorem pullStructure_inv_one (x : structureCohomology A.X 1) :
    pullStructure A ι[A.X] 1 x = -x := by
  let p₁ : A.X ⨯ A.X ⟶ A.X := prod.fst
  let p₂ : A.X ⨯ A.X ⟶ A.X := prod.snd
  let i : A.X ⟶ A.X ⨯ A.X := prod.lift (𝟙 A.X) ι[A.X]
  have h₁ : i ≫ p₁ = 𝟙 _ := prod.lift_fst _ _
  have h₂ : i ≫ p₂ = ι[A.X] := prod.lift_snd _ _
  have hm : i ≫ (p₁ * p₂) = Over.homMk A.X.hom ≫ η[A.X] := by
    rw [MonObj.comp_mul, h₁, h₂]
    change (𝟙 A.X) * (𝟙 A.X)⁻¹ = _
    rw [mul_inv_cancel, Hom.one_def]
    congr 1
  have h := congrArg (unitCohomologyPullbackLinear i 1) (pullStructure_mul A x)
  change unitCohomologyPullbackLinear i 1 (unitCohomologyPullbackLinear (p₁ * p₂) 1 x) =
    unitCohomologyPullbackLinear i 1 (unitCohomologyPullbackLinear p₁ 1 x +
      unitCohomologyPullbackLinear p₂ 1 x) at h
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← unitCohomologyPullback_comp, ← unitCohomologyPullback_comp,
    ← unitCohomologyPullback_comp, hm, h₁, h₂,
    unitCohomologyPullback_base η[A.X] 0, unitCohomologyPullback_id] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [LinearMap.zero_apply, LinearMap.id_apply,
    add_comm] using h.symm)

private lemma pullStructure_inv_cup (x y : structureCohomology A.X 1) :
    pullStructure A ι[A.X] 2 (cupA A x y) = cupA A x y := by
  let g : A.X ⟶ A.X := ι[A.X]
  let W : coverIdx A × coverIdx A → A.X.left.Opens := fun ij =>
    cover A ij.1 ⊓ g.left ⁻¹ᵁ cover A ij.2
  have : IsIso g.left := (Over.forget _).map_isIso g
  have hWaff (ij) : IsAffineOpen (W ij) := by
    have : A.X.left.IsSeparated := ⟨by
      rw [← terminal.comp_from A.X.hom]
      infer_instance⟩
    exact (cover_affine A ij.1).inf ((cover_affine A ij.2).preimage_of_isIso g.left)
  have hW : ⨆ ij, W ij = ⊤ := by
    rw [iSup_prod]
    simp only [W, ← inf_iSup_eq, ← g.left.preimage_iSup, cover_top, Scheme.Hom.preimage_top,
      inf_top_eq]
  have h := pull_cupCanonical g (cover A) W Prod.snd (fun _ => inf_le_right)
    (cover_top A) hW (cover_affine A) hWaff x y
  change pullStructure A ι[A.X] 2 (cupA A x y) =
    cupCanonical A.X.hom W hW hWaff (pullStructure A ι[A.X] 1 x) (pullStructure A ι[A.X] 1 y) at h
  rw [cupCanonical_refine A.X.hom (cover A) W Prod.fst (fun _ => inf_le_left)
    (cover_top A) hW (cover_affine A) hWaff, pullStructure_inv_one, pullStructure_inv_one] at h
  simpa only [cupA, map_neg, LinearMap.neg_apply, neg_neg] using h

/-- Inversion is the identity in degree two because cup products of degree-one classes
span degree two. -/
theorem pullStructure_inv_two (x : structureCohomology A.X 2) :
    pullStructure A ι[A.X] 2 x = x := by
  let D := CARData.toCARFamily A fieldStructureSheafH1Dimension (canonicalCARData A)
  let t := pullStructure A ι[A.X] 2 - LinearMap.id
  have htop : (⨆ i, (D.c i 1).range) = ⊤ :=
    Langlands.LinearAlgebra.BoundedCreationContraction.iSup_range_degreeOne_eq_top
      D.c D.d D.rel D.bound
  have h : (⨆ i, (D.c i 1).range) ≤ t.ker := by
    refine iSup_le fun i => ?_
    rintro _ ⟨y, rfl⟩
    change pullStructure A ι[A.X] 2 (D.c i 1 y) - D.c i 1 y = 0
    rw [D.c_one, pullStructure_inv_cup, sub_self]
  rw [htop] at h
  have hx := LinearMap.mem_ker.mp (h (Submodule.mem_top (x := x)))
  exact sub_eq_zero.mp hx

end Langlands.AbelianScheme
