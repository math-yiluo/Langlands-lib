import Langlands.Geometry.Building.UnramifiedZeroFixerAffineRootStatement
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.Geometry.Building.UnramifiedSharpFixerRootGenerationProof
import Langlands.Geometry.Building.UnramifiedZeroFixerSharpComparisonProof

/-! # Zero-group fixers depend only on nonnegative affine roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

private instance unramifiedZeroFixerProofAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

private theorem mem_fixingSubgroup_smul_image {M X : Type*} [Group M] [MulAction M X]
    (g h : M) (Y : Set X) :
    h ∈ fixingSubgroup M ((fun y => g • y) '' Y) ↔
      g⁻¹ * h * g ∈ fixingSubgroup M Y := by
  rw [mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  simp only [Set.forall_mem_image]
  constructor
  · intro hh y hy
    simp only [mul_smul, hh hy, inv_smul_smul]
  · intro hh y hy
    have heq := congrArg (fun z => g • z) (hh y hy)
    simpa only [mul_smul, smul_inv_smul] using heq

private theorem normal_inf_fixingSubgroup_image_eq {M X : Type*} [Group M] [MulAction M X]
    (H : Subgroup M) (hH : H.Normal) (g : M) {Y Y' : Set X}
    (h : H ⊓ fixingSubgroup M Y = H ⊓ fixingSubgroup M Y') :
    H ⊓ fixingSubgroup M ((fun y => g • y) '' Y) =
      H ⊓ fixingSubgroup M ((fun y => g • y) '' Y') := by
  ext x
  have hconj : x ∈ H ↔ g⁻¹ * x * g ∈ H := by
    constructor
    · intro hx
      simpa only [inv_inv] using hH.conj_mem x hx g⁻¹
    · intro hx
      have hx' := hH.conj_mem (g⁻¹ * x * g) hx g
      simpa [mul_assoc] using hx'
  rw [Subgroup.mem_inf, Subgroup.mem_inf,
    mem_fixingSubgroup_smul_image, mem_fixingSubgroup_smul_image, hconj]
  exact SetLike.ext_iff.mp h (g⁻¹ * x * g)

/-- Pointwise fixers in the zero subgroup of translated nonempty bounded apartment
subsets depend only on the affine roots nonnegative on those subsets. -/
theorem unramifiedZeroFixerAffineRoot :
    UnramifiedZeroFixerAffineRootStatement.{u} := by
  intro F _ _ _ _ G _ C E g Ω Ω' hΩ hbΩ hΩ' hbΩ' hroots
  have hsharp : C.sharpFixer Ω = C.sharpFixer Ω' := by
    rw [unramifiedSharpFixerRootGeneration F _ C Ω hΩ,
      unramifiedSharpFixerRootGeneration F _ C Ω' hΩ']
    apply iSup_congr
    intro a
    apply iSup_congr
    intro ψ
    apply iSup_congr
    intro hψ
    apply iSup_congr
    intro hlin
    exact iSup_congr_Prop (hroots ψ hψ) fun _ => rfl
  have hfix :
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') := by
    rw [unramifiedZeroFixerSharpComparison F _ C E Ω hΩ hbΩ,
      unramifiedZeroFixerSharpComparison F _ C E Ω' hΩ' hbΩ', hsharp]
  have hnormal : E.zeroPoints.Normal :=
    normal_of_simplyConnectedImage_le E.isSimplyConnectedDerivedCover
      E.simplyConnectedImage_le_zeroPoints
  have htranslated := normal_inf_fixingSubgroup_image_eq E.zeroPoints hnormal g hfix
  simpa only [Set.image_image, Function.comp_apply,
    IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.pointwiseFixer] using htranslated

end Langlands.Geometry.Building
