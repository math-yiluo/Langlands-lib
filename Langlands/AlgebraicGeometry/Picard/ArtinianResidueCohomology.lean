import Langlands.AlgebraicGeometry.Picard.ArtinianResidueSheaf
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic

/-! # Actual elementary ideal cohomology as residue-fibre tensor coefficients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueCohomology

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite ArtinianResidueSections ArtinianResidueSheaf

section FiniteProducts

variable {Y : Scheme.{u}} {R : CommRingCat.{u}} (p : Y ⟶ Spec R)
  (M : Y.Modules) (ι : Type u) [Finite ι]

/-- Actual relative cohomology preserves a finite product, with source-ring scalars. -/
def finiteProductCohomologyIso (n : ℕ) :
    (relativeCohomology p n).obj (∏ᶜ fun _ : ι => M) ≅
      ModuleCat.of R (ι → (relativeCohomology p n).obj M) := by
  letI : (relativeCohomology p n).Additive :=
    Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive
      (relativeGlobalSections p) n
  exact PreservesProduct.iso (relativeCohomology p n) (fun _ : ι => M) ≪≫
    ModuleCat.piIsoPi _

/-- Coordinates are the cohomology maps of the actual sheaf projections. -/
lemma finiteProductCohomologyIso_apply (n : ℕ)
    (x : (relativeCohomology p n).obj (∏ᶜ fun _ : ι => M)) (j : ι) :
    (finiteProductCohomologyIso p M ι n).hom x j =
      (relativeCohomology p n).map (Pi.π (fun _ : ι => M) j) x := by
  let : (relativeCohomology p n).Additive :=
    Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive
      (relativeGlobalSections p) n
  have h := congrArg (fun a => a
    ((PreservesProduct.iso (relativeCohomology p n) (fun _ : ι => M)).hom x))
    (ModuleCat.piIsoPi_hom_ker_subtype
      (fun _ : ι => (relativeCohomology p n).obj M) j)
  change (finiteProductCohomologyIso p M ι n).hom x j = _
  simp only [finiteProductCohomologyIso, Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply]
  exact h.trans (congrArg (fun a => a x)
    (piComparison_comp_π (relativeCohomology p n) (fun _ : ι => M) j))

end FiniteProducts

section VectorCoordinates

variable {K V H ι : Type u} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup H] [Module K H] [Finite ι] (b : Module.Basis ι K V)

/-- Finite-basis tensor coordinates for an arbitrary coefficient module. -/
def vectorTensorCoordinates : H ⊗[K] V ≃ₗ[K] (ι → H) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisRight b).trans
    (Finsupp.linearEquivFunOnFinite K H ι)

@[simp]
lemma vectorTensorCoordinates_tmul (x : H) (v : V) (j : ι) :
    vectorTensorCoordinates b (x ⊗ₜ[K] v) j = b.repr v j • x := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b x v j

end VectorCoordinates

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local notation "pA" => NatTrans.app (relativeProjection f) (ArtinianTest.base A)
local notation "pK" => NatTrans.app (relativeProjection f) (ArtinianTest.residueBase k K)
local notation "i" => residueMap f A

local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq

/-- The residue map is the actual base change of the closed residue immersion. -/
lemma residueMap_isClosedImmersion : IsClosedImmersion i :=
  relativeSpace_map_property f @IsClosedImmersion (ArtinianTest.reduction A)
    (ArtinianTest.reduction_isClosedImmersion A)

/-- The actual square retains the specified residue augmentation. -/
lemma residueMap_projection :
    i ≫ pA = pK ≫ Spec.map (CommRingCat.ofHom A.augmentation.toRingHom) :=
  (relativeProjection f).naturality (ArtinianTest.reduction A)

/-- Cohomology of the actual residue-fibre structure module. -/
abbrev ResidueCohomology (n : ℕ) :=
  (relativeCohomology pK n).obj
    (SheafOfModules.unit
      ((relativeSpace f).obj (ArtinianTest.residueBase k K)).ringCatSheaf)

/-- Residue pushforward cohomology, with the actual augmentation restriction of scalars. -/
def residueStructureCohomologyIso (n : ℕ) :
    (relativeCohomology pA n).obj (residueStructureModule f (A := A)) ≅
      (ModuleCat.restrictScalars A.augmentation.toRingHom).obj
        (ResidueCohomology (K := K) f n) := by
  letI := residueMap_isClosedImmersion f (A := A)
  let O := SheafOfModules.unit
    ((relativeSpace f).obj (ArtinianTest.residueBase k K)).ringCatSheaf
  letI : O.IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit _
  exact (affinePushforwardCohomologyIso i pA O n).symm ≪≫
    (relativeCohomologyBaseRingIso (CommRingCat.ofHom A.augmentation.toRingHom)
      (i ≫ pA) pK (residueMap_projection f) n).app O

variable {ι : Type u} [Finite ι] (b : Module.Basis ι K (Kernel q))

variable [Flat f]

attribute [local instance] ArtinianPicardObstructionFinite.sourceModule

/-- Actual ideal cohomology coordinates, retaining the source-ring action. -/
def idealCohomologyCoordinates (n : ℕ) :
    Cohomology f q n ≃ₗ[A.algebra]
      (ι → (ModuleCat.restrictScalars A.augmentation.toRingHom).obj
        (ResidueCohomology (K := K) f n)) :=
  (relativeEquiv f q n).trans
    (((relativeCohomology pA n).mapIso (residueProductIdealIso f q b).symm).toLinearEquiv.trans
      ((finiteProductCohomologyIso pA (residueStructureModule f (A := A)) ι n).toLinearEquiv.trans
        (LinearEquiv.piCongrRight fun _ =>
          (residueStructureCohomologyIso f (A := A) n).toLinearEquiv)))

variable [IsProper f]

/-- The same coordinates respect the canonical descended residue-field action. -/
def idealResidueCohomologyCoordinates (n : ℕ) :
    letI := ArtinianPicardObstructionFinite.residueModule f q hq n
    Cohomology f q n ≃ₗ[K] (ι → ResidueCohomology (K := K) f n) := by
  letI := ArtinianPicardObstructionFinite.residueModule f q hq n
  refine
    { (idealCohomologyCoordinates f q b n).toAddEquiv with
      map_smul' := ?_ }
  intro c x
  obtain ⟨a, rfl⟩ := A.augmentation_surjective c
  rw [augmentation_smul f q hq n]
  exact (idealCohomologyCoordinates f q b n).map_smul a x

/-- The actual elementary ideal cohomology is residue-fibre cohomology tensored with its kernel. -/
def idealCohomologyTensorEquiv (n : ℕ) :
    letI := ArtinianPicardObstructionFinite.residueModule f q hq n
    Cohomology f q n ≃ₗ[K] ResidueCohomology (K := K) f n ⊗[K] Kernel q := by
  letI := ArtinianPicardObstructionFinite.residueModule f q hq n
  exact (idealResidueCohomologyCoordinates f q b n).trans (vectorTensorCoordinates b).symm

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueCohomology
