import Langlands.Cohomology.CompactSoft.Statement

/-!
# Reducing smooth Godement c-softness to coinduced stalk families
-/

noncomputable section

namespace Langlands.Cohomology.CompactSoft

open CategoryTheory Langlands.Sheaf.Equivariant Langlands.Sheaf.CompactSoft

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- The ordinary Godement comparison, carried through coinduction, the smooth
part, and forgetting equivariance. -/
def smoothCoinducedZeroIso (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (toSheaf G X (ModuleCat.{u} R)).obj
      ((smoothSubsheafFunctor R).obj
        ((coinduction G X (ModuleCat.{u} R)).obj
          ((toSheaf G X (ModuleCat.{u} R)).obj (Godement.zeroSheaf F.obj)))) ≅
    (toSheaf G X (ModuleCat.{u} R)).obj
      ((smoothSubsheafFunctor R).obj
        ((coinduction G X (ModuleCat.{u} R)).obj
          ((Langlands.Sheaf.Godement.zeroFunctor
            (Langlands.Cohomology.Flasque.spacePoints (TopCat.of X))
            (ModuleCat.{u} R)).obj ((toSheaf G X (ModuleCat.{u} R)).obj F)))) :=
  (toSheaf G X (ModuleCat.{u} R)).mapIso
    ((smoothSubsheafFunctor R).mapIso
      ((coinduction G X (ModuleCat.{u} R)).mapIso ((Godement.zeroIso R G X).app F)))

/-- The published ordinary Godement comparison transports c-softness of the
smooth part of coinduced stalk families to the assigned smooth Godement target. -/
theorem smoothGodementZeroCSoft_of_coinducedZero
    (h : ∀ F : TopologicalSheaf G X (ModuleCat.{u} R),
      IsCSoft ((toSheaf G X (ModuleCat.{u} R)).obj
        ((smoothSubsheafFunctor R).obj
          ((coinduction G X (ModuleCat.{u} R)).obj
            ((toSheaf G X (ModuleCat.{u} R)).obj (Godement.zeroSheaf F.obj)))))) :
    SmoothGodementZeroCSoftStatement R G X := by
  intro M
  let F := (smoothInclusion R G X).obj M
  exact (h F).of_iso (smoothCoinducedZeroIso F)

end Langlands.Cohomology.CompactSoft
