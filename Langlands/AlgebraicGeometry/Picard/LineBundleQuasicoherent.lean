import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Quasi-coherence of actual locally free rank-one sheaves -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {X Y : Scheme.{u}}

private lemma isQuasicoherent_over_of_trivialization {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (M.over U).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    (Langlands.Scheme.Modules.unitLocalBasis e)
    (inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf.over U)
      PUnit.{u + 1}).IsQuasicoherent)

/-- Local trivializations of an actual rank-one sheaf give quasi-coherence. -/
lemma IsLocallyFreeRankOne.isQuasicoherent {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) : M.IsQuasicoherent := by
  classical
  choose U hx e using hM
  have hU : (_root_.Opens.grothendieckTopology X).CoversTop U := by
    apply (_root_.Opens.coversTop_iff X U).mpr
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have (x : X) : (M.over (U x)).IsQuasicoherent :=
    isQuasicoherent_over_of_trivialization (e x).some
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hU

/-- The underlying sheaf of an actual line bundle is quasi-coherent. -/
instance LineBundle.isQuasicoherent (L : LineBundle X) : L.obj.IsQuasicoherent :=
  L.property.isQuasicoherent

/-- Regard actual line bundles and their morphisms as quasi-coherent sheaves. -/
def LineBundle.toQuasicoherent (X : Scheme.{u}) :
    LineBundle X ⥤ (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (LineBundle.forget X) (fun L => L.property.isQuasicoherent)

/-- Forgetting quasi-coherence recovers the underlying module sheaf functor. -/
def LineBundle.toQuasicoherentCompForgetIso (X : Scheme.{u}) :
    LineBundle.toQuasicoherent X ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ≅
        LineBundle.forget X :=
  Iso.refl _

/-- Pullback of a locally free rank-one sheaf is quasi-coherent. -/
lemma IsLocallyFreeRankOne.isQuasicoherent_pullback {M : Y.Modules}
    (hM : IsLocallyFreeRankOne M) (f : X ⟶ Y) :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  (hM.pullback f).isQuasicoherent

end Langlands.AlgebraicGeometry.Picard
