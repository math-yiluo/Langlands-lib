import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingProof
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingProof

/-! # Actual line bundles glued over arbitrary scheme open covers -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace LineBundleOpenCover

/-- Local rank one can be checked on any scheme open cover. -/
lemma rankOne_of_cover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) {M : X.Modules}
    (h : ∀ i, IsLocallyFreeRankOne ((Scheme.Modules.pullback (𝒰.f i)).obj M)) :
    IsLocallyFreeRankOne M := by
  intro x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact IsLocallyFreeRankOne.exists_of_pullback _ (h i) y

end LineBundleOpenCover

/-- Descent data for actual line bundles on a scheme open cover. The overlap
condition is the module-sheaf cocycle on the actual pairwise and triple
scheme pullbacks. -/
structure LineBundleGluingData {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) where
  /-- The line bundle on each cover member. -/
  bundle : ∀ i, LineBundle (𝒰.X i)
  /-- The identification on each ordered pairwise overlap. -/
  transition : ∀ i j,
    (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (bundle i).obj ≅
      (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (bundle j).obj
  /-- The compatibility on triple overlaps, including repeated indices. -/
  cocycle : Langlands.Scheme.Modules.OpenCoverModuleGluing.CocycleCondition
    𝒰 (fun i ↦ (bundle i).obj) transition

namespace LineBundleGluingData

variable {X : Scheme.{u}} {𝒰 : X.OpenCover.{u}} (D : LineBundleGluingData 𝒰)

/-- The underlying module obtained by the published module-sheaf gluing. -/
def gluedModule : X.Modules :=
  Langlands.Scheme.Modules.OpenCoverModuleGluing.glued
    𝒰 (fun i ↦ (D.bundle i).obj) D.transition

/-- The comparison of the actual pullback of the glued module with a piece. -/
def moduleIso (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (𝒰.f i)).obj D.gluedModule ≅ (D.bundle i).obj :=
  Langlands.Scheme.Modules.OpenCoverModuleGluing.pieceIso
    𝒰 (fun i ↦ (D.bundle i).obj) D.transition D.cocycle i

/-- The glued module is locally free of rank one. -/
lemma gluedModule_rankOne : IsLocallyFreeRankOne D.gluedModule :=
  LineBundleOpenCover.rankOne_of_cover 𝒰
    (fun i ↦ (D.bundle i).property.of_iso (D.moduleIso i).symm)

/-- The actual glued line bundle. -/
def glue : LineBundle X := ⟨D.gluedModule, D.gluedModule_rankOne⟩

/-- Pulling the glued line bundle back to a cover member gives that piece. -/
def iso (i : 𝒰.I₀) : (LineBundle.pullback (𝒰.f i)).obj D.glue ≅ D.bundle i :=
  ObjectProperty.isoMk _ (D.moduleIso i)

/-- The chosen comparisons realize the prescribed overlap identifications. -/
lemma moduleIso_compatible (i j : 𝒰.I₀) :
    (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).map
        (D.moduleIso i).hom ≫ (D.transition i j).hom =
      (Langlands.Scheme.Modules.squarePullbackIso (𝒰.f j)
        (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
        (𝒰.f i) pullback.condition D.gluedModule).hom ≫
          (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).map
            (D.moduleIso j).hom :=
  Langlands.Scheme.Modules.OpenCoverModuleGluing.CompEq2.eq
    (Langlands.Scheme.Modules.OpenCoverModuleGluing.pieceIso_compat D.cocycle i j)

end LineBundleGluingData

end Langlands.AlgebraicGeometry.Picard
