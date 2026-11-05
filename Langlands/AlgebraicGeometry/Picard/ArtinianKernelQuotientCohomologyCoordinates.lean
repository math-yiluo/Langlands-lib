import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientCoordinates
import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientTensor
import Langlands.AlgebraicGeometry.Modules.DerivedSectionsLinear

/-! # Finite coordinates on actual quotient cohomology -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCohomologyCoordinates

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardKernelTensor ArtinianSquareZeroPicardLifting
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueSections ArtinianResidueSheaf ArtinianResidueCohomology
open ArtinianKernelQuotientResidue ArtinianKernelQuotientSheaf
open ArtinianKernelQuotientCohomology ArtinianResidueCohomologyQuotient
open ArtinianKernelQuotientCoordinates

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

attribute [local instance] sectionAlgebra residueSectionAlgebra
  ArtinianResidueKernel.residueSourceAlgebra

/-- Source scalars restrict to their specified residue scalars on every open. -/
lemma residue_testSectionHom (A : ArtinianTest k K)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (a : A.algebra) :
    (residueMap f A).app U (testSectionHom f A U a) =
      residueSectionHom f ((residueMap f A) ⁻¹ᵁ U) (A.augmentation a) :=
  ArtinianKernelQuotientTensor.baseScalar_naturality (residueMap f A)
    ((relativeProjection f).app (ArtinianTest.base A))
    ((relativeProjection f).app (ArtinianTest.residueBase k K))
    (CommRingCat.ofHom A.augmentation.toRingHom) (residueMap_projection f) U a

/-- On the actual residue pushforward, base scalar sheaf maps have residue scalar sections. -/
lemma residue_scalarHom_app (A : ArtinianTest k K) {M : ((relativeSpace f).obj
      (ArtinianTest.base A)).Modules}
    (a : M ⟶ residueStructureModule f (A := A)) (r : A.algebra)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (s : Γ(M, U)) :
    (Langlands.Scheme.Modules.scalarHom
        (Langlands.Scheme.Modules.scalarsFromBase
          ((relativeProjection f).app (ArtinianTest.base A)) r) a).app U s =
      A.augmentation r • (show Γ((relativeSpace f).obj
        (ArtinianTest.residueBase k K), (residueMap f A) ⁻¹ᵁ U) from a.app U s) := by
  rw [Langlands.Scheme.Modules.scalarHom_app]
  change (residueMap f A).app U (testSectionHom f A U r) *
    (show Γ((relativeSpace f).obj (ArtinianTest.residueBase k K),
      (residueMap f A) ⁻¹ᵁ U) from a.app U s) = _
  rw [residue_testSectionHom]
  rfl

/-- Finite-product cohomology coordinates in the actual residue-fibre cohomology,
retaining restriction along the specified source augmentation. -/
def residueProductCohomologyCoordinates (A : ArtinianTest k K)
    (ι : Type u) [Finite ι] (n : ℕ) :
    (relativeCohomology ((relativeProjection f).app (ArtinianTest.base A)) n).obj
        (residueProductModule f (A := A) ι) ≃ₗ[A.algebra]
      (ι → (ModuleCat.restrictScalars A.augmentation.toRingHom).obj
        (ResidueCohomology (K := K) f n)) :=
  (finiteProductCohomologyIso ((relativeProjection f).app (ArtinianTest.base A))
      (residueStructureModule f (A := A)) ι n).toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun _ =>
      (residueStructureCohomologyIso f (A := A) n).toLinearEquiv)

lemma residueProductCohomologyCoordinates_apply (A : ArtinianTest k K)
    (ι : Type u) [Finite ι] (n : ℕ)
    (x : (relativeCohomology ((relativeProjection f).app (ArtinianTest.base A)) n).obj
      (residueProductModule f (A := A) ι)) (j : ι) :
    residueProductCohomologyCoordinates f A ι n x j =
      (residueStructureCohomologyIso f (A := A) n).hom
        ((relativeCohomology ((relativeProjection f).app (ArtinianTest.base A)) n).map
          (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j) x) := by
  change (residueStructureCohomologyIso f (A := A) n).hom
    ((finiteProductCohomologyIso ((relativeProjection f).app (ArtinianTest.base A))
      (residueStructureModule f (A := A)) ι n).hom x j) = _
  rw [finiteProductCohomologyIso_apply]

variable {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq
variable (W : Submodule K (Kernel q))

local notation "AQ" => ElementaryKernelSubspaceQuotient.test q W
local notation "π" => ElementaryKernelSubspaceQuotient.projection q W
local notation "r" => ElementaryKernelSubspaceQuotient.reduction q W
local notation "h" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap π)
local notation "pA" => NatTrans.app (relativeProjection f) (ArtinianTest.base A)
local notation "pQ" => NatTrans.app (relativeProjection f) (ArtinianTest.base AQ)
local notation "φ" => CommRingCat.ofHom (AlgHom.toRingHom (ArtinianTest.toAlgHom π))

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)
local instance : IsClosedImmersion h :=
  relativeMap_isClosedImmersion f π
    (ElementaryKernelSubspaceQuotient.projection_elementary q W).1

variable {ι κ : Type u} [Finite ι] [Finite κ]
  (b : Module.Basis ι K (Kernel q))
  (c : Module.Basis κ K
    (Kernel (ElementaryKernelSubspaceQuotient.reduction q W)))

local instance : Fintype ι := Fintype.ofFinite ι

/-- A quotient coordinate is the finite sum of scalar source projections,
followed by the actual residue identification. -/
lemma quotientProductMap_projection (l : κ) (a : ι → A.algebra)
    (ha : ∀ j, A.augmentation (a j) = kernelQuotientMatrix q W b c l j) :
    quotientProductMap f q W b c ≫ (Scheme.Modules.pushforward h).map
        (Pi.π (fun _ : κ => residueStructureModule f (A := AQ)) l) =
      (∑ j, Langlands.Scheme.Modules.scalarHom
        (Langlands.Scheme.Modules.scalarsFromBase pA (a j))
          (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j)) ≫
        (residueQuotientIso f q W).hom := by
  classical
  ext U s
  change (Pi.π (fun _ : κ => residueStructureModule f (A := AQ)) l).app
      ((h) ⁻¹ᵁ U) ((quotientProductMap f q W b c).app U s) = _
  rw [← productSectionsIso_apply]
  change residueProductSectionsEquiv f κ ((h) ⁻¹ᵁ U)
      ((quotientProductMap f q W b c).app U s) l = _
  rw [quotientProductMap_coordinates f q W b c, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, residueQuotientIso_app]
  have hs : (∑ j, Langlands.Scheme.Modules.scalarHom
      (Langlands.Scheme.Modules.scalarsFromBase pA (a j))
        (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j)).app U s =
      ∑ j, A.augmentation (a j) •
        (show Γ((relativeSpace f).obj (ArtinianTest.residueBase k K),
          (residueMap f A) ⁻¹ᵁ U) from
          (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j).app U s) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Scheme.Modules.Hom.add_app]
      change (_ : Γ(residueStructureModule f (A := A), U)) + _ = _
      erw [ih, residue_scalarHom_app]
  erw [hs, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, ha j]
  rw [show residueProductSectionsEquiv f ι U s j =
    (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j).app U s from
      productSectionsIso_apply _ _ U s j]

/-- The actual quotient cohomology map has the matrix of the actual kernel quotient
in the actual residue-fibre coordinates. -/
lemma quotientProductCohomologyMap_coordinates (n : ℕ)
    (x : (relativeCohomology pA n).obj (residueProductModule f (A := A) ι)) (l : κ) :
    residueProductCohomologyCoordinates f AQ κ n
        (quotientProductCohomologyMap f q W b c n x) l =
      ∑ j, kernelQuotientMatrix q W b c l j •
        (show ResidueCohomology (K := K) f n from
          residueProductCohomologyCoordinates f A ι n x j) := by
  classical
  choose a ha using fun j : ι =>
    A.augmentation_surjective (kernelQuotientMatrix q W b c l j)
  let t : residueProductModule f (A := A) ι ⟶ residueStructureModule f (A := A) :=
    ∑ j, Langlands.Scheme.Modules.scalarHom
      (Langlands.Scheme.Modules.scalarsFromBase pA (a j))
        (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j)
  have ht : (relativeCohomology pA n).map t =
      ∑ j, a j • (relativeCohomology pA n).map
        (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j) := by
    dsimp only [t]
    change relativeCohomologyHomLinearMap pA n _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact relativeCohomology_map_scalarHom pA n (a j)
      (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j)
  have htx : (relativeCohomology pA n).map t x =
      ∑ j, a j • (relativeCohomology pA n).map
        (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j) x := by
    change ((relativeCohomology pA n).map t).hom x = _
    rw [ht, ModuleCat.hom_sum]
    simp only [LinearMap.sum_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
    rfl
  have hs := quotientProductMap_projection f q W b c l a ha
  have hn := closedImmersionCohomologyMap_naturality φ pA pQ h
    (projection_square f q W) (quotientProductMap f q W b c)
    (t ≫ (residueQuotientIso f q W).hom) (𝟙 _)
    (Pi.π (fun _ : κ => residueStructureModule f (A := AQ)) l)
    (by simpa only [Category.id_comp, t] using hs.symm) n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hx := congrArg (fun m => m x) hn
  change closedImmersionCohomologyMap φ pA pQ h (projection_square f q W)
      (t ≫ (residueQuotientIso f q W).hom) n x =
    (relativeCohomology pQ n).map
      (Pi.π (fun _ : κ => residueStructureModule f (A := AQ)) l)
      (quotientProductCohomologyMap f q W b c n x) at hx
  rw [residueProductCohomologyCoordinates_apply, ← hx,
    closedImmersionCohomologyMap_precomp]
  change (residueStructureCohomologyIso f (A := AQ) n).hom
    (closedImmersionCohomologyMap φ pA pQ h (projection_square f q W)
      (residueQuotientIso f q W).hom n ((relativeCohomology pA n).map t x)) = _
  rw [residueStructureCohomologyIso_quotient, htx, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  change A.augmentation (a j) •
    (show ResidueCohomology (K := K) f n from
      (residueStructureCohomologyIso f (A := A) n).hom
        ((relativeCohomology pA n).map
          (Pi.π (fun _ : ι => residueStructureModule f (A := A)) j) x)) = _
  rw [ha j, residueProductCohomologyCoordinates_apply]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCohomologyCoordinates
