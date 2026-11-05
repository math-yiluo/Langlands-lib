import Langlands.AlgebraicGeometry.Picard.ArtinianSquareZeroPicardLifting
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof
import Mathlib.Algebra.Module.RingHom
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Finite residue-field modules on actual Artinian Picard obstruction spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules
open StructureKernelModule

namespace ArtinianPicardObstructionFinite

private lemma shortComplex_smul_eq_zero {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (a : R)
    (h : ∀ x : S.X₂, a • x = 0) (x : S.homology) : a • x = 0 := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  have hy : a • y = 0 := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    change S.iCycles.hom (a • y) = S.iCycles.hom 0
    rw [map_smul, h, map_zero]
  change a • S.homologyπ.hom y = 0
  rw [← map_smul, hy, map_zero]

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)

/-- The actual ideal module on the source test scheme. -/
abbrev idealModule :=
  kernelModule ((relativeSpace f).map (ArtinianTest.baseMap q))

/-- The original proper structure map stays proper over every actual test ring. -/
instance projection_isProper [IsProper f] (A : ArtinianTest k K) :
    IsProper ((relativeProjection f).app (ArtinianTest.base A)) :=
  inferInstanceAs (IsProper (Limits.pullback.fst (ArtinianTest.base A).hom f))

/-- The actual relative ideal has finite cohomology over the Artinian source ring. -/
lemma relativeCohomology_finite [IsProper f] (hq : Function.Surjective (ArtinianTest.toAlgHom q))
    (n : ℕ) :
    Module.Finite A.algebra
      ((DerivedSections.relativeCohomology
        ((relativeProjection f).app (ArtinianTest.base A)) n).obj (idealModule f q)) := by
  let : IsClosedImmersion ((relativeSpace f).map (ArtinianTest.baseMap q)) :=
    ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f q hq
  let : IsLocallyNoetherian ((Over.forget _).obj (ArtinianTest.base A)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A.algebra)))
  have : IsLocallyNoetherian ((relativeSpace f).obj (ArtinianTest.base A)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((relativeProjection f).app (ArtinianTest.base A))
  exact (properCoherentCohomologyFinite A.algebra _ _
    inferInstance (idealModule f q) (kernelModule_isQuasicoherent _)
      (kernelModule_hasFiniteAffineSections _)).1 n

/-- The maximal ideal annihilates actual affine sections of an elementary relative ideal. -/
lemma affineSections_smul_eq_zero (hq : ArtinianTest.IsElementarySurjection q)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (a : A.algebra) (ha : a ∈ IsLocalRing.maximalIdeal A.algebra)
    (x : (OModulePresheaf.ofModules
      ((relativeProjection f).app (ArtinianTest.base A)) (idealModule f q)).obj U) :
    a • x = 0 := by
  apply Subtype.ext
  change ArtinianSquareZeroPicardLifting.testSectionHom f A U a * x.val = 0
  have hx : x.val ∈ (RingHom.ker (ArtinianTest.toAlgHom q).toRingHom).map
      (ArtinianSquareZeroPicardLifting.testSectionHom f A U) := by
    rw [← ArtinianSquareZeroPicardLifting.relativeMap_affine_ker f q hq.1 U hU]
    exact x.property
  have ha' := Ideal.mem_map_of_mem
    (ArtinianSquareZeroPicardLifting.testSectionHom f A U) ha
  have hz : (IsLocalRing.maximalIdeal A.algebra).map
      (ArtinianSquareZeroPicardLifting.testSectionHom f A U) *
        (RingHom.ker (ArtinianTest.toAlgHom q).toRingHom).map
          (ArtinianSquareZeroPicardLifting.testSectionHom f A U) = ⊥ := by
    rw [← Ideal.map_mul, hq.2, Ideal.map_bot]
  exact Ideal.mem_bot.mp (hz ▸ Ideal.mul_mem_mul ha' hx)

/-- The maximal ideal annihilates every actual relative ideal-cohomology class. -/
lemma relativeCohomology_smul_eq_zero [IsProper f]
    (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ)
    (a : A.algebra) (ha : a ∈ IsLocalRing.maximalIdeal A.algebra)
    (x : (DerivedSections.relativeCohomology
      ((relativeProjection f).app (ArtinianTest.base A)) n).obj (idealModule f q)) :
    a • x = 0 := by
  let : IsClosedImmersion ((relativeSpace f).map (ArtinianTest.baseMap q)) :=
    ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f q hq.1
  let : (idealModule f q).IsQuasicoherent := kernelModule_isQuasicoherent _
  let p := (relativeProjection f).app (ArtinianTest.base A)
  let 𝒰 := CechResolution.orderedAffineCoverOfQuasiCompact p
  let C := CechResolution.cechCochainComplex p 𝒰 (idealModule f q)
  let e := (CechResolution.cechCohomologyIso p 𝒰 (idealModule f q) n).toLinearEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← e.map_smul]
  have hy : a • y = 0 := by
    apply shortComplex_smul_eq_zero (C.sc n) a
    intro z
    change a • (z : (OModulePresheaf.ofModules p (idealModule f q)).cochain 𝒰 n) = 0
    funext s
    exact affineSections_smul_eq_zero f q hq _ (CechResolution.isAffineOpen_inter p 𝒰 s)
      a ha (z s)
  rw [hy, map_zero]

/-- The unchanged ideal-cohomology group used by the actual Picard obstruction. -/
abbrev Cohomology (n : ℕ) :=
  SquareZeroUnitCohomology.idealCohomology
    ((relativeSpace f).map (ArtinianTest.baseMap q)) n

/-- Restrict the actual global-ring action along the relative structure map. -/
@[instance_reducible]
def sourceModule (n : ℕ) : Module A.algebra (Cohomology f q n) :=
  Module.compHom _ (DerivedSections.structureRingHom
    ((relativeProjection f).app (ArtinianTest.base A))).hom

attribute [local instance] sourceModule

/-- The canonical comparison with the actual relative cohomology, with its source-ring action. -/
def relativeEquiv (n : ℕ) :
    Cohomology f q n ≃ₗ[A.algebra]
      (DerivedSections.relativeCohomology
        ((relativeProjection f).app (ArtinianTest.base A)) n).obj (idealModule f q) :=
  ((DerivedSections.relativeCohomologyRestrictScalarsIso
    ((relativeProjection f).app (ArtinianTest.base A)) n).app
      (idealModule f q)).toLinearEquiv

/-- The actual ideal-cohomology group is finite over the Artinian source ring. -/
lemma cohomology_finite [IsProper f] (hq : Function.Surjective (ArtinianTest.toAlgHom q))
    (n : ℕ) : Module.Finite A.algebra (Cohomology f q n) := by
  let := relativeCohomology_finite f q hq n
  exact Module.Finite.equiv (relativeEquiv f q n).symm

/-- The maximal ideal annihilates the unchanged actual obstruction-cohomology group. -/
lemma cohomology_smul_eq_zero [IsProper f] (hq : ArtinianTest.IsElementarySurjection q)
    (n : ℕ) (a : A.algebra) (ha : a ∈ IsLocalRing.maximalIdeal A.algebra)
    (x : Cohomology f q n) : a • x = 0 := by
  apply (relativeEquiv f q n).injective
  rw [map_smul, map_zero]
  exact relativeCohomology_smul_eq_zero f q hq n a ha _

variable [IsProper f]

/-- The augmentation kernel annihilates actual ideal cohomology for an elementary arrow. -/
lemma augmentation_ker_le_annihilator (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ) :
    RingHom.ker A.augmentation.toRingHom ≤
      Module.annihilator A.algebra (Cohomology f q n) := by
  intro a ha
  exact Module.mem_annihilator.mpr fun x ↦
    cohomology_smul_eq_zero f q hq n a (ArtinianTest.ker_augmentation A ▸ ha) x

/-- Descend the actual source-ring action on ideal cohomology to the specified residue field. -/
def residueAction (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ) :
    K →+* AddMonoid.End (Cohomology f q n) :=
  A.augmentation.toRingHom.liftOfSurjective A.augmentation_surjective
    ⟨Module.toAddMonoidEnd A.algebra (Cohomology f q n),
      augmentation_ker_le_annihilator f q hq n⟩

lemma residueAction_augmentation (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ)
    (a : A.algebra) :
    residueAction f q hq n (A.augmentation a) =
      Module.toAddMonoidEnd A.algebra (Cohomology f q n) a :=
  RingHom.liftOfSurjective_comp_apply _ _ _ a

/-- The descended action is uniquely determined by recovery of the actual source-ring action. -/
lemma residueAction_unique (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ)
    (ρ : K →+* AddMonoid.End (Cohomology f q n))
    (hρ : ρ.comp A.augmentation.toRingHom =
      Module.toAddMonoidEnd A.algebra (Cohomology f q n)) :
    ρ = residueAction f q hq n :=
  RingHom.eq_liftOfSurjective _ _ _ _ ρ hρ

/-- The residue-field module on the unchanged actual ideal-cohomology group. -/
@[instance_reducible]
def residueModule (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ) :
    Module K (Cohomology f q n) :=
  Module.compHom _ (residueAction f q hq n)

/-- The residue-field scalars recover the actual source-ring scalars through augmentation. -/
@[simp]
lemma augmentation_smul (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ)
    (a : A.algebra) (x : Cohomology f q n) :
    letI := residueModule f q hq n
    A.augmentation a • x = a • x := by
  change residueAction f q hq n (A.augmentation a) x = a • x
  rw [residueAction_augmentation]
  rfl

/-- The actual additive identity is semilinear for the augmentation. -/
def identitySemilinear (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ) :
    letI := residueModule f q hq n
    Cohomology f q n →ₛₗ[A.augmentation.toRingHom] Cohomology f q n := by
  let := residueModule f q hq n
  exact
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ (augmentation_smul f q hq n a x).symm }

/-- Every actual elementary ideal-cohomology group is finite dimensional over the residue field. -/
lemma finiteDimensional (hq : ArtinianTest.IsElementarySurjection q) (n : ℕ) :
    letI := residueModule f q hq n
    FiniteDimensional K (Cohomology f q n) := by
  let := residueModule f q hq n
  let := cohomology_finite f q hq.1 n
  exact Module.Finite.of_surjective (identitySemilinear f q hq n) Function.surjective_id

end ArtinianPicardObstructionFinite

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
