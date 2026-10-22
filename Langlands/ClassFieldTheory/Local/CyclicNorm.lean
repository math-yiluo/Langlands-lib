import Langlands.ClassFieldTheory.Local.UnitInvariants
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.Cohomology.Tate.ZeroDefinitions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Cyclic relative H2 and the actual determinant norm quotient -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Fixed units descend to the unique unit of the base field mapping to them. -/
def invariantUnitsEquiv : (unitsRepresentation K L).ρ.invariants ≃+ Additive Kˣ :=
  (baseUnitsEquivInvariants K L).symm

variable [Fintype Gal(L/K)]

/-- Descent takes the representation norm to the actual field norm. -/
theorem invariantUnitsEquiv_norm (x : Additive Lˣ) :
    invariantUnitsEquiv K L (Langlands.Tate.normToInvariants
      (unitsRepresentation K L) x) =
      Additive.ofMul (Langlands.LocalClassField.normUnits K L x.toMul) := by
  apply (invariantUnitsEquiv K L).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change (Langlands.Tate.normToInvariants (unitsRepresentation K L) x) =
    baseUnitsToInvariants K L _
  apply Subtype.ext
  exact unitsRepresentation_norm K L x.toMul

/-- Fixed units map to their descended class in the actual field norm quotient. -/
def invariantNormProjection : (unitsRepresentation K L).ρ.invariants →+
    Additive (Langlands.LocalClassField.NormQuotient K L) :=
  (Langlands.LocalClassField.normQuotientProjection K L).toAdditive.comp
    (invariantUnitsEquiv K L).toAddMonoidHom

omit [Fintype Gal(L/K)] in
private theorem invariantNormProjection_surjective :
    Function.Surjective (invariantNormProjection K L) := by
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (Langlands.LocalClassField.normSubgroup K L) x.toMul
  refine ⟨(invariantUnitsEquiv K L).symm (Additive.ofMul a), ?_⟩
  change Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L
    ((invariantUnitsEquiv K L) ((invariantUnitsEquiv K L).symm _)).toMul) = x
  simpa [Langlands.LocalClassField.normQuotientProjection] using congrArg Additive.ofMul ha

/-- The kernel of descent modulo field norms is exactly the representation norm image. -/
private theorem invariantNormProjection_ker :
    (invariantNormProjection K L).ker =
      (Langlands.Tate.normImage (unitsRepresentation K L)).toAddSubgroup := by
  ext x
  change (Langlands.LocalClassField.normQuotientProjection K L)
    ((invariantUnitsEquiv K L) x).toMul = 1 ↔
      x ∈ Langlands.Tate.normImage (unitsRepresentation K L)
  change (↑((invariantUnitsEquiv K L) x).toMul :
    Langlands.LocalClassField.NormQuotient K L) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply (invariantUnitsEquiv K L).injective
    rw [invariantUnitsEquiv_norm]
    exact congrArg Additive.ofMul hy
  · rintro ⟨y, rfl⟩
    rw [invariantUnitsEquiv_norm]
    exact ⟨y.toMul, rfl⟩

private def submoduleQuotientAddEquiv {R A : Type*} [Ring R] [AddCommGroup A]
    [Module R A] (N : Submodule R A) : (A ⧸ N) ≃+ (A ⧸ N.toAddSubgroup) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def quotientByKernelEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (N : AddSubgroup A) (f : A →+ B) (h : N = f.ker) (hf : Function.Surjective f) :
    A ⧸ N ≃+ B :=
  (QuotientAddGroup.quotientAddEquivOfEq h).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

/-- Invariant units modulo their group norm identify with the actual field norm quotient. -/
def invariantsModNormEquiv :
    Langlands.Tate.InvariantsModNorm (unitsRepresentation K L) ≃+
      Additive (Langlands.LocalClassField.NormQuotient K L) :=
  (submoduleQuotientAddEquiv (Langlands.Tate.normImage (unitsRepresentation K L))).trans
    (quotientByKernelEquiv (B := Additive (Langlands.LocalClassField.NormQuotient K L))
    (Langlands.Tate.normImage (unitsRepresentation K L)).toAddSubgroup
    (invariantNormProjection K L) (invariantNormProjection_ker K L).symm
    (invariantNormProjection_surjective K L))

/-- On representatives, the quotient equivalence descends the invariant unit and takes its class. -/
theorem invariantsModNormEquiv_mk (x : (unitsRepresentation K L).ρ.invariants) :
    invariantsModNormEquiv K L (Submodule.Quotient.mk x) =
      invariantNormProjection K L x := rfl

/-- The inverse sends the class of a base-field unit to the class of its inclusion. -/
theorem invariantsModNormEquiv_symm_projection (a : Additive Kˣ) :
    (invariantsModNormEquiv K L).symm
      ((Langlands.LocalClassField.normQuotientProjection K L).toAdditive a) =
        Submodule.Quotient.mk (baseUnitsToInvariants K L a) := by
  apply (invariantsModNormEquiv K L).injective
  rw [AddEquiv.apply_symm_apply, invariantsModNormEquiv_mk]
  change _ = (Langlands.LocalClassField.normQuotientProjection K L).toAdditive
    ((invariantUnitsEquiv K L) ((invariantUnitsEquiv K L).symm a))
  rw [AddEquiv.apply_symm_apply]

private def cyclicKernelEquivInvariants {R G : Type v} [CommRing R]
    [CommGroup G] [Fintype G] (A : Rep R G) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (Rep.FiniteCyclicGroup.normHomCompSub A σ).g.hom.ker ≃ₗ[R] A.ρ.invariants :=
  LinearEquiv.ofEq _ _ (by
    ext x
    simpa [Rep.sub_hom, sub_eq_zero] using
      (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ x).symm)

private theorem cyclicKernelEquivInvariants_map_range {R G : Type v} [CommRing R]
    [CommGroup G] [Fintype G] (A : Rep R G) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (Rep.FiniteCyclicGroup.normHomCompSub A σ).moduleCatToCycles.range.map
      (cyclicKernelEquivInvariants A σ hσ).toLinearMap = Langlands.Tate.normImage A := by
  rw [← LinearMap.range_comp]
  congr 1

/-- The cyclic-resolution comparison from actual ordinary H2 to invariant units modulo norms. -/
def cyclicH2InvariantsEquiv (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    relativeCohomology K L 2 ≃ₗ[IntegerScalars.{v}]
      Langlands.Tate.InvariantsModNorm (unitsRepresentation K L) := by
  letI : IsCyclic Gal(L/K) := ⟨σ, hσ⟩
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A := unitsRepresentation K L
  let S := Rep.FiniteCyclicGroup.normHomCompSub A σ
  let e := Rep.FiniteCyclicGroup.groupCohomologyIsoEven A σ hσ 2 (by decide)
  exact (e ≪≫ S.moduleCatHomologyIso).toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (cyclicKernelEquivInvariants A σ hσ)
      (cyclicKernelEquivInvariants_map_range A σ hσ))

omit [Fintype Gal(L/K)] in
/-- For the specified generator, ordinary relative H2 is the actual field norm quotient. -/
def cyclicH2NormEquiv (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    relativeCohomology K L 2 ≃+
      Additive (Langlands.LocalClassField.NormQuotient K L) := by
  letI := Fintype.ofFinite Gal(L/K)
  exact (cyclicH2InvariantsEquiv K L σ hσ).toAddEquiv.trans (invariantsModNormEquiv K L)

end Langlands.ClassFieldTheory.Local
