import Langlands.AlgebraicGeometry.Modules.ClosedImmersionCohomologyComposition
import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientCohomology

/-! # Residue cohomology across an elementary kernel quotient -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueCohomologyQuotient

open Langlands.AlgebraicGeometry.Modules.DerivedSections

section Factorization

variable {Y Z T : Scheme.{u}} {R S V : CommRingCat.{u}}
  (φ : R ⟶ S) (ψ : S ⟶ V) (θ : R ⟶ V)
  (g : Y ⟶ Spec R) (g' : Z ⟶ Spec S) (g'' : T ⟶ Spec V)
  (h : Z ⟶ Y) (j : T ⟶ Z) (i : T ⟶ Y)
  (ei : j ≫ h = i)

/-- Identify a direct pushforward with the actual successive pushforwards. -/
def factorizationPushforwardIso (P : T.Modules) :
    (Scheme.Modules.pushforward i).obj P ≅
      (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pushforward j).obj P) :=
  (Scheme.Modules.pushforwardCongr ei.symm).app P ≪≫
    (Scheme.Modules.pushforwardComp j h).symm.app P

private lemma closedImmersionCohomologyMap_factorization
    [IsClosedImmersion h] [IsClosedImmersion j] [IsClosedImmersion i]
    (w : h ≫ g = g' ≫ Spec.map φ)
    (w' : j ≫ g' = g'' ≫ Spec.map ψ)
    (w0 : i ≫ g = g'' ≫ Spec.map θ) (eθ : φ ≫ ψ = θ)
    (P : T.Modules) (n : ℕ)
    (x : (relativeCohomology g n).obj ((Scheme.Modules.pushforward i).obj P)) :
    closedImmersionCohomologyMap ψ g' g'' j w' (𝟙 _) n
        (closedImmersionCohomologyMap φ g g' h w
          (factorizationPushforwardIso h j i ei P).hom n x) =
      closedImmersionCohomologyMap θ g g'' i w0 (𝟙 _) n x := by
  subst i
  subst θ
  have hc := closedImmersionCohomologyMap_comp φ ψ g g' g'' h j w w'
    ((Scheme.Modules.pushforwardComp j h).inv.app P) (𝟙 _) n
  have he : (Scheme.Modules.pushforwardCongr (rfl : j ≫ h = j ≫ h)).hom.app P = 𝟙 _ := by
    ext U s
    simp
  have hf : (factorizationPushforwardIso h j (j ≫ h) rfl P).hom =
      (Scheme.Modules.pushforwardComp j h).inv.app P := by
    change (Scheme.Modules.pushforwardCongr rfl).hom.app P ≫
      (Scheme.Modules.pushforwardComp j h).inv.app P = _
    rw [he, Category.id_comp]
  rw [hf]
  simp only [compositePushforwardModuleMap, CategoryTheory.Functor.map_id,
    Category.id_comp] at hc
  rw [show (Scheme.Modules.pushforwardComp j h).inv.app P ≫
      (Scheme.Modules.pushforwardComp j h).hom.app P = 𝟙 _ from
        ((Scheme.Modules.pushforwardComp j h).app P).inv_hom_id] at hc
  exact (congrArg (fun a => a x) hc).symm

end Factorization

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueSections ArtinianResidueSheaf ArtinianResidueCohomology ArtinianKernelQuotientSheaf
open ArtinianKernelQuotientResidue

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq
variable (W : Submodule K (Kernel q))

local notation "AQ" => ElementaryKernelSubspaceQuotient.test q W
local notation "π" => ElementaryKernelSubspaceQuotient.projection q W
local notation "h" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap π)
local notation "iA" => residueMap f A
local notation "iQ" => residueMap f AQ
local notation "pA" => NatTrans.app (relativeProjection f) (ArtinianTest.base A)
local notation "pQ" => NatTrans.app (relativeProjection f) (ArtinianTest.base AQ)
local notation "pK" => NatTrans.app (relativeProjection f) (ArtinianTest.residueBase k K)
local notation "φ" => CommRingCat.ofHom (AlgHom.toRingHom (ArtinianTest.toAlgHom π))

local instance : IsClosedImmersion h :=
  ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f π
    (ElementaryKernelSubspaceQuotient.projection_elementary q W).1
local instance : IsClosedImmersion iA := residueMap_isClosedImmersion f (A := A)
local instance : IsClosedImmersion iQ := residueMap_isClosedImmersion f (A := AQ)

/-- The actual identification of the two residue pushforwards over a quotient. -/
def residueQuotientIso :
    residueStructureModule f (A := A) ≅
      (Scheme.Modules.pushforward h).obj (residueStructureModule f (A := AQ)) :=
  factorizationPushforwardIso h iQ iA (residue_factorization f q W)
    (SheafOfModules.unit ((relativeSpace f).obj (ArtinianTest.residueBase k K)).ringCatSheaf)

/-- The canonical cohomology map identifies both pushed residue structures
with the very same residue-fibre cohomology. -/
lemma residueStructureCohomologyIso_quotient (n : ℕ)
    (x : (relativeCohomology pA n).obj (residueStructureModule f (A := A))) :
    (residueStructureCohomologyIso f (A := AQ) n).hom
        (closedImmersionCohomologyMap φ pA pQ h (projection_square f q W)
          (residueQuotientIso f q W).hom n x) =
      (residueStructureCohomologyIso f (A := A) n).hom x := by
  have hh := closedImmersionCohomologyMap_factorization φ
    (CommRingCat.ofHom (AQ).augmentation.toRingHom)
    (CommRingCat.ofHom A.augmentation.toRingHom) pA pQ pK h iQ iA
    (residue_factorization f q W) (projection_square f q W)
    (residueMap_projection f (A := AQ)) (residueMap_projection f (A := A))
    (by
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom (ArtinianTest.augmentation_comp π))
    (SheafOfModules.unit ((relativeSpace f).obj (ArtinianTest.residueBase k K)).ringCatSheaf) n x
  simp only [closedImmersionCohomologyMap, residueStructureCohomologyIso,
    affinePushforwardCohomologyIso, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.trans_hom, Iso.symm_hom, ConcreteCategory.comp_apply,
    residueQuotientIso, residueStructureModule, ResidueCohomology, Iso.app_hom] at hh ⊢
  convert hh using 1

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueCohomologyQuotient
