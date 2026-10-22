import Langlands.ClassFieldTheory.Local.FixedFieldUnits
import Langlands.ClassFieldTheory.Local.RelativeH1Proof

noncomputable section

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L]

/-- The kernel of normal restriction to the middle field. -/
abbrev towerRestrictionKernel : Subgroup Gal(M/K) :=
  (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker

/-- The kernel acts precisely as the automorphisms over the middle field. -/
def towerRestrictionKernelEquiv : towerRestrictionKernel K L M ≃* Gal(M/L) where
  toFun σ :=
    { σ.1 with
      commutes' := fun x =>
        (σ.1.restrictNormal_commutes L x).symm.trans
          (congrArg (algebraMap L M) (AlgEquiv.ext_iff.mp σ.2 x)) }
  invFun σ := ⟨σ.restrictScalars K, by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M).injective
    exact ((σ.restrictScalars K).restrictNormal_commutes L x).trans (σ.commutes x)⟩
  left_inv σ := by apply Subtype.ext; exact AlgEquiv.ext fun _ => rfl
  right_inv σ := AlgEquiv.ext fun _ => rfl
  map_mul' σ τ := AlgEquiv.ext fun _ => rfl

@[simp]
theorem towerRestrictionKernelEquiv_symm_val (σ : Gal(M/L)) :
    ((towerRestrictionKernelEquiv K L M).symm σ).1 = σ.restrictScalars K := rfl

/-- Inclusion of units, with codomain the actual kernel invariants. -/
def towerInvariantUnitInclusion :
    Additive Lˣ →ₗ[IntegerScalars.{u}] fixedUnitSubmodule K M (towerRestrictionKernel K L M) :=
  (unitInclusionLinear L M).codRestrict _ fun x σ => by
    apply Units.ext
    exact ((towerRestrictionKernelEquiv K L M σ).commutes x.toMul.val)

/-- Unit inclusion remains injective after restricting its codomain. -/
theorem towerInvariantUnitInclusion_injective :
    Function.Injective (towerInvariantUnitInclusion K L M) := by
  intro x y h
  apply Units.ext
  apply (algebraMap L M).injective
  exact congrArg (fun z : fixedUnitSubmodule K M (towerRestrictionKernel K L M) =>
    z.1.toMul.val) h

/-- The kernel restriction coefficients are the actual upper relative coefficients. -/
def towerKernelCohomologyIso (n : ℕ) :
    groupCohomology (Rep.res (towerRestrictionKernel K L M).subtype
      (unitsRepresentation K M)) n ≅ relativeCohomology L M n :=
  groupCohomology.mapIso (towerRestrictionKernelEquiv K L M)
    (LinearEquiv.refl _ (Additive Mˣ)) (fun _ => rfl) n

/-- Restriction through the kernel comparison is the published field restriction. -/
theorem towerKernelCohomologyIso_restriction (n : ℕ) :
    groupCohomology.map (towerRestrictionKernel K L M).subtype (𝟙 _) n ≫
      (towerKernelCohomologyIso K L M n).hom = relativeRestriction K L M n := by
  rw [towerKernelCohomologyIso, groupCohomology.mapIso_hom, ← groupCohomology.map_comp]
  exact groupCohomology.map_congr rfl rfl n

variable [FiniteDimensional K M] [IsGalois K M]

/-- Every invariant unit comes from the middle field. -/
theorem towerInvariantUnitInclusion_surjective :
    Function.Surjective (towerInvariantUnitInclusion K L M) := by
  intro x
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x.1.toMul.val).2
    (fun σ => congrArg (fun z : Additive Mˣ => z.toMul.val)
      (x.2 ((towerRestrictionKernelEquiv K L M).symm σ)))
  have hy0 : y ≠ 0 := by
    intro h
    apply x.1.toMul.ne_zero
    rw [← hy, h, map_zero]
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hy

/-- Actual units of the middle field identify with kernel invariant units. -/
def towerInvariantUnitsEquiv :
    Additive Lˣ ≃ₗ[IntegerScalars.{u}]
      fixedUnitSubmodule K M (towerRestrictionKernel K L M) :=
  LinearEquiv.ofBijective (towerInvariantUnitInclusion K L M)
    ⟨towerInvariantUnitInclusion_injective K L M,
      towerInvariantUnitInclusion_surjective K L M⟩

/-- The quotient by the restriction kernel is the middle Galois group. -/
def towerQuotientEquiv : Gal(M/K) ⧸ towerRestrictionKernel K L M ≃* Gal(L/K) :=
  QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom_surjective M)

omit [FiniteDimensional K M] in
@[simp]
theorem towerQuotientEquiv_mk (σ : Gal(M/K)) :
    towerQuotientEquiv K L M (QuotientGroup.mk σ) = σ.restrictNormal L := rfl

/-- Unit inclusion intertwines the quotient action with restriction of automorphisms. -/
theorem towerInvariantUnitsEquiv_intertwines (σ : Gal(M/K)) :
    (towerInvariantUnitsEquiv K L M).toLinearMap ∘ₗ
        (unitsRepresentation K L).ρ (σ.restrictNormal L) =
      ((unitsRepresentation K M).quotientToInvariants (towerRestrictionKernel K L M)).ρ
          (QuotientGroup.mk σ) ∘ₗ (towerInvariantUnitsEquiv K L M).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  exact σ.restrictNormal_commutes L x.toMul.val

/-- Cohomology of quotient invariant units identifies with middle relative cohomology. -/
def towerQuotientCohomologyIso (n : ℕ) :
    groupCohomology ((unitsRepresentation K M).quotientToInvariants
      (towerRestrictionKernel K L M)) n ≅ relativeCohomology K L n :=
  groupCohomology.mapIso (towerQuotientEquiv K L M)
    (towerInvariantUnitsEquiv K L M).symm (fun g => by
      induction g using QuotientGroup.induction_on with
      | H σ =>
        apply LinearMap.ext
        intro x
        apply (towerInvariantUnitsEquiv K L M).injective
        let e := towerInvariantUnitsEquiv K L M
        let ρ := ((unitsRepresentation K M).quotientToInvariants
          (towerRestrictionKernel K L M)).ρ
        change e (e.symm (ρ (QuotientGroup.mk σ) x)) =
          e ((unitsRepresentation K L).ρ (σ.restrictNormal L) (e.symm x))
        rw [e.apply_symm_apply]
        have h := LinearMap.congr_fun (towerInvariantUnitsEquiv_intertwines K L M σ)
          (e.symm x)
        change e ((unitsRepresentation K L).ρ (σ.restrictNormal L) (e.symm x)) =
          ρ (QuotientGroup.mk σ) (e (e.symm x)) at h
        rw [e.apply_symm_apply] at h
        exact h.symm) n

/-- Inflation through the quotient comparison is the published field inflation. -/
theorem towerQuotientCohomologyIso_inflation (n : ℕ) :
    (towerQuotientCohomologyIso K L M n).inv ≫
      groupCohomology.map (QuotientGroup.mk' (towerRestrictionKernel K L M))
        (Rep.ofHom <| (unitsRepresentation K M).ρ.quotientToInvariants_lift
          (towerRestrictionKernel K L M)) n = relativeInflation K L M n := by
  rw [towerQuotientCohomologyIso, groupCohomology.mapIso_inv, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr rfl
  rfl

omit [IsGalois K M] in
/-- Hilbert 90 for the actual restriction to the normal kernel. -/
theorem towerKernelH1_subsingleton :
    Subsingleton (groupCohomology (Rep.res (towerRestrictionKernel K L M).subtype
      (unitsRepresentation K M)) 1) := by
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : Subsingleton (relativeCohomology L M 1) := finiteRelativeH1Vanishing L M
  exact (ModuleCat.mono_iff_injective (towerKernelCohomologyIso K L M 1).hom).mp
    inferInstance |>.subsingleton

end Langlands.ClassFieldTheory.Local
