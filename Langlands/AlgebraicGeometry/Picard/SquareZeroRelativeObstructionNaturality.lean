import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyMap
import Langlands.AlgebraicGeometry.Picard.SquareZeroAmbientObstructionNaturality

/-! # Actual square-zero Picard obstruction in relative module cohomology -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroRelativeObstructionNaturality

open Langlands.AlgebraicGeometry.Modules
open Modules.PushforwardInjectiveAcyclic
open SquareZeroUnitCohomology SquareZeroAmbientObstructionNaturality
open SquareZeroPicardObstruction StructureKernelModule UnitSheafPushforward

/-- The unchanged actual ideal cohomology with scalars restricted along the
specified structure morphism. -/
def relativeIdealCohomologyAddEquiv {X Z : Scheme.{u}} {R : CommRingCat.{u}}
    (p : X ⟶ Spec R) (i : Z ⟶ X) (n : ℕ) :
    idealCohomology i n ≃+
      (DerivedSections.relativeCohomology p n).obj (kernelModule i) :=
  ((DerivedSections.relativeCohomologyRestrictScalarsIso p n).app
    (kernelModule i)).toLinearEquiv.toAddEquiv

variable {X Y Z : Scheme.{u}} (b : Y ⟶ X) (j : Z ⟶ Y)
  [IsClosedImmersion b] (hb : IsNilpotent b.ker)
  {R S : CommRingCat.{u}} (φ : R ⟶ S)
  (p : X ⟶ Spec R) (p' : Y ⟶ Spec S) (w : b ≫ p = p' ≫ Spec.map φ)

/-- The actual ambient ideal-cohomology map agrees with the canonical relative
closed-immersion cohomology map for the actual kernel-module morphism. -/
lemma idealCohomologyMap_relative (n : ℕ) (x : idealCohomology (j ≫ b) n) :
    (DerivedSections.relativeCohomologyRestrictScalarsIso p' n).hom.app (kernelModule j)
        (idealCohomologyMap b j hb n x) =
      DerivedSections.closedImmersionCohomologyMap φ p p' b w (kernelModuleMap b j) n
        ((DerivedSections.relativeCohomologyRestrictScalarsIso p n).hom.app
          (kernelModule (j ≫ b)) x) := by
  let e := nilpotentClosedImmersionTopIso b hb
  have : IsIso b.base := by
    change IsIso e.hom
    infer_instance
  have he : asIso b.base = e := by
    apply Iso.ext
    rfl
  have h := AbelianSheafComparison.relativeHAddEquiv_closedImmersionCohomologyMap
    b p φ p' w (kernelModuleMap b j) n ((idealCohomologyAddEquiv (j ≫ b) n).symm x)
  have hc (e₁ e₂ : Y.toTopCat ≅ X.toTopCat) (heq : e₁ = e₂) :
      HEq (cohomologyPushforwardEquiv e₁ ((toAbSheaf Y).obj (kernelModule j)) n)
        (cohomologyPushforwardEquiv e₂ ((toAbSheaf Y).obj (kernelModule j)) n) := by
    cases heq
    rfl
  have hc' := eq_of_heq (hc (asIso b.base) e he)
  rw [hc'] at h
  have hs : AbelianSheafComparison.relativeHAddEquiv p (kernelModule (j ≫ b)) n
      ((idealCohomologyAddEquiv (j ≫ b) n).symm x) =
      (DerivedSections.relativeCohomologyRestrictScalarsIso p n).hom.app
        (kernelModule (j ≫ b)) x := by
    change (DerivedSections.relativeCohomologyRestrictScalarsIso p n).hom.app
        (kernelModule (j ≫ b))
        (idealCohomologyAddEquiv (j ≫ b) n
          ((idealCohomologyAddEquiv (j ≫ b) n).symm x)) = _
    rw [AddEquiv.apply_symm_apply]
  rw [hs] at h
  exact h.symm

variable [IsClosedImmersion j] [CompactSpace Z]

include hb

/-- The actual Picard obstruction is natural for the canonical relative
cohomology map, with the specified affine-base square retained. -/
lemma obstructionMap_relative (hj : j.ker ^ 2 = ⊥) (hjb : (j ≫ b).ker ^ 2 = ⊥)
    (y : Group Z) :
    (DerivedSections.relativeCohomologyRestrictScalarsIso p' 2).hom.app (kernelModule j)
        (obstructionMap j hj y) =
      DerivedSections.closedImmersionCohomologyMap φ p p' b w (kernelModuleMap b j) 2
        ((DerivedSections.relativeCohomologyRestrictScalarsIso p 2).hom.app
          (kernelModule (j ≫ b)) (obstructionMap (j ≫ b) hjb y)) := by
  rw [obstructionMap_naturality b j hj hjb hb y]
  exact idealCohomologyMap_relative b j hb φ p p' w 2 _

/-- An actual factorization equality transports the source kernel and its
obstruction into the same canonical closed-immersion map. -/
lemma obstructionMap_factorization {i : Z ⟶ X} (wi : j ≫ b = i)
    [IsClosedImmersion i] (hj : j.ker ^ 2 = ⊥) (hi : i.ker ^ 2 = ⊥)
    (y : Group Z) :
    (DerivedSections.relativeCohomologyRestrictScalarsIso p' 2).hom.app (kernelModule j)
        (obstructionMap j hj y) =
      DerivedSections.closedImmersionCohomologyMap φ p p' b w
        (eqToHom (congrArg kernelModule wi.symm) ≫ kernelModuleMap b j) 2
        ((DerivedSections.relativeCohomologyRestrictScalarsIso p 2).hom.app
          (kernelModule i) (obstructionMap i hi y)) := by
  cases wi
  simpa only [eqToHom_refl, Category.id_comp] using
    obstructionMap_relative b j hb φ p p' w hj hi y

end Langlands.AlgebraicGeometry.Picard.SquareZeroRelativeObstructionNaturality
