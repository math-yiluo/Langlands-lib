import Langlands.ClassField.Global.CohomologyMaps
import Langlands.ClassField.Global.IdeleClassGaloisDescentStatement
import Langlands.ClassFieldTheory.Local.FiniteTowerCohomology
import Langlands.Cohomology.H2InflationProof

/-! # Conditional inflation–restriction for actual idele-class cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open CategoryTheory NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

variable (F E L : Type u) [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

/-- The actual coefficient submodule fixed by the kernel of restriction to `E`. -/
abbrev ideleClassTowerInvariants :=
  Representation.invariants
    ((relativeIdeleClassRepresentation F L).ρ.comp (towerRestrictionKernel F E L).subtype)

/-- Inclusion of idele classes, corestricted to the kernel invariants. -/
def ideleClassTowerInvariantInclusion :
    (relativeIdeleClassRepresentation F E).V →ₗ[ULift.{u} ℤ]
      ideleClassTowerInvariants F E L :=
  (ideleClassInclusionLinear F E L).codRestrict _ fun x σ => by
    have h := Rep.hom_comm_apply (ideleClassInflationCoefficients F E L) σ.1 x
    change ideleClassInclusionLinear F E L
        ((relativeIdeleClassRepresentation F E).ρ (AlgEquiv.restrictNormalHom E σ.1) x) =
      (relativeIdeleClassRepresentation F L).ρ σ.1 (ideleClassInclusionLinear F E L x) at h
    have hσ : AlgEquiv.restrictNormalHom E σ.1 = 1 := σ.2
    rw [hσ, map_one] at h
    exact h.symm

variable (hdesc : IdeleClassGaloisDescent.{u, u})

/-- Galois descent identifies actual lower idele classes with the kernel invariants. -/
def ideleClassTowerInvariantsEquiv :
    (relativeIdeleClassRepresentation F E).V ≃ₗ[ULift.{u} ℤ]
      ideleClassTowerInvariants F E L := by
  let := IsGalois.tower_top_of_isGalois F E L
  apply LinearEquiv.ofBijective (ideleClassTowerInvariantInclusion F E L)
  constructor
  · intro x y h
    apply Additive.toMul.injective
    apply (hdesc E L).1
    exact congrArg (fun z : ideleClassTowerInvariants F E L => z.val.toMul) h
  · intro x
    have hx : ∀ σ : L ≃ₐ[E] L, relativeIdeleClassAut E L σ x.val.toMul = x.val.toMul := by
      intro σ
      exact congrArg Additive.toMul (x.property ((towerRestrictionKernelEquiv F E L).symm σ))
    obtain ⟨a, ha⟩ := ((hdesc E L).2 x.val.toMul).mp hx
    refine ⟨Additive.ofMul a, Subtype.ext ?_⟩
    exact congrArg Additive.ofMul ha

omit [NumberField F] in
/-- The invariant-coefficient equivalence intertwines the quotient Galois action. -/
theorem ideleClassTowerInvariantsEquiv_intertwines (σ : L ≃ₐ[F] L) :
    (ideleClassTowerInvariantsEquiv F E L hdesc).toLinearMap ∘ₗ
        (relativeIdeleClassRepresentation F E).ρ (σ.restrictNormal E) =
      ((relativeIdeleClassRepresentation F L).quotientToInvariants
        (towerRestrictionKernel F E L)).ρ (QuotientGroup.mk σ) ∘ₗ
          (ideleClassTowerInvariantsEquiv F E L hdesc).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact Rep.hom_comm_apply (ideleClassInflationCoefficients F E L) σ x

/-- Cohomology with quotient-invariant coefficients is the lower idele-class cohomology. -/
def ideleClassTowerQuotientCohomologyIso (n : ℕ) :
    groupCohomology ((relativeIdeleClassRepresentation F L).quotientToInvariants
      (towerRestrictionKernel F E L)) n ≅ relativeIdeleClassCohomology F E n :=
  groupCohomology.mapIso (towerQuotientEquiv F E L)
    (ideleClassTowerInvariantsEquiv F E L hdesc).symm (fun g => by
      induction g using QuotientGroup.induction_on with
      | H σ =>
        apply LinearMap.ext
        intro x
        let e := ideleClassTowerInvariantsEquiv F E L hdesc
        let ρ := ((relativeIdeleClassRepresentation F L).quotientToInvariants
          (towerRestrictionKernel F E L)).ρ
        apply e.injective
        change e (e.symm (ρ (QuotientGroup.mk σ) x)) =
          e ((relativeIdeleClassRepresentation F E).ρ (σ.restrictNormal E) (e.symm x))
        rw [e.apply_symm_apply]
        have h := LinearMap.congr_fun
          (ideleClassTowerInvariantsEquiv_intertwines F E L hdesc σ) (e.symm x)
        change e ((relativeIdeleClassRepresentation F E).ρ (σ.restrictNormal E) (e.symm x)) =
          ρ (QuotientGroup.mk σ) (e (e.symm x)) at h
        rw [e.apply_symm_apply] at h
        exact h.symm) n

omit [NumberField F] in
/-- Under the quotient comparison, abstract inflation is actual idele-class inflation. -/
theorem ideleClassTowerQuotientCohomologyIso_inflation (n : ℕ) :
    (ideleClassTowerQuotientCohomologyIso F E L hdesc n).inv ≫
      groupCohomology.map (QuotientGroup.mk' (towerRestrictionKernel F E L))
        (Rep.ofHom <| (relativeIdeleClassRepresentation F L).ρ.quotientToInvariants_lift
          (towerRestrictionKernel F E L)) n = relativeIdeleClassInflation F E L n := by
  rw [ideleClassTowerQuotientCohomologyIso, groupCohomology.mapIso_inv,
    ← groupCohomology.map_comp]
  apply groupCohomology.map_congr rfl
  rfl

/-- Restriction to the normal kernel has the actual upper relative coefficients. -/
def ideleClassTowerKernelCohomologyIso (n : ℕ) :
    groupCohomology (Rep.res (towerRestrictionKernel F E L).subtype
      (relativeIdeleClassRepresentation F L)) n ≅ relativeIdeleClassCohomology E L n :=
  groupCohomology.mapIso (towerRestrictionKernelEquiv F E L)
    (LinearEquiv.refl _ _) (fun _ => rfl) n

omit [NumberField F] [NumberField E] [IsGalois F L] in
/-- Under the kernel comparison, abstract restriction is actual idele-class restriction. -/
theorem ideleClassTowerKernelCohomologyIso_restriction (n : ℕ) :
    groupCohomology.map (towerRestrictionKernel F E L).subtype (𝟙 _) n ≫
      (ideleClassTowerKernelCohomologyIso F E L n).hom =
        relativeIdeleClassRestriction F E L n := by
  rw [ideleClassTowerKernelCohomologyIso, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp]
  exact groupCohomology.map_congr rfl rfl n

include hdesc in
omit [NumberField F] in
/-- With object descent and vanishing of upper relative `H¹`, actual inflation in
degree two is injective and its image is the kernel of actual restriction. -/
theorem ideleClassH2InflationExactness_of
    (hH1 : Subsingleton (relativeIdeleClassCohomology E L 1)) :
    Function.Injective (relativeIdeleClassInflation F E L 2) ∧
      LinearMap.range (relativeIdeleClassInflation F E L 2).hom =
        LinearMap.ker (relativeIdeleClassRestriction F E L 2).hom := by
  let := hH1
  have hkernel : Subsingleton (groupCohomology
      (Rep.res (towerRestrictionKernel F E L).subtype
        (relativeIdeleClassRepresentation F L)) 1) :=
    (ModuleCat.mono_iff_injective (ideleClassTowerKernelCohomologyIso F E L 1).hom).mp
      inferInstance |>.subsingleton
  let C := groupCohomology.HInfRes (relativeIdeleClassRepresentation F L)
    (towerRestrictionKernel F E L) 2
  obtain ⟨hinj, hexact⟩ := Langlands.Cohomology.h2InflationRestrictionExactness
    (ULift.{u} ℤ) (L ≃ₐ[F] L) (relativeIdeleClassRepresentation F L)
    (towerRestrictionKernel F E L) hkernel
  let q := ideleClassTowerQuotientCohomologyIso F E L hdesc 2
  let e := ideleClassTowerKernelCohomologyIso F E L 2
  have hi : q.inv ≫ C.f = relativeIdeleClassInflation F E L 2 :=
    ideleClassTowerQuotientCohomologyIso_inflation F E L hdesc 2
  have hr : C.g ≫ e.hom = relativeIdeleClassRestriction F E L 2 :=
    ideleClassTowerKernelCohomologyIso_restriction F E L 2
  have hqi : Function.Injective q.inv :=
    (ModuleCat.mono_iff_injective q.inv).mp inferInstance
  have hqs : Function.Surjective q.inv :=
    (ModuleCat.epi_iff_surjective q.inv).mp inferInstance
  have hei : Function.Injective e.hom :=
    (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  constructor
  · rw [← hi]
    exact hinj.comp hqi
  · rw [← hi, ← hr]
    change LinearMap.range (C.f.hom.comp q.inv.hom) =
      LinearMap.ker (e.hom.hom.comp C.g.hom)
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hqs),
      LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hei)]
    exact hexact

end Langlands.ClassField.Global
