import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomologyNaturalityStatement

/-! # Functorial residue-fibre coefficient maps on original schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

open StructureKernelModule Langlands.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) [IsLocalRing S]

/-- The actual residue-fibre projection to the original scheme. -/
abbrev residueι (X : Over (Spec (CommRingCat.of R))) :
    ((residuePullback φ).obj X).left ⟶ X.left :=
  pullback.fst X.hom (residueBaseMap φ)

/-- The structure module of the actual residue fibre, pushed to the original scheme. -/
abbrev residueModule (X : Over (Spec (CommRingCat.of R))) : X.left.Modules :=
  (Scheme.Modules.pushforward (residueι φ X)).obj
    (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf)

/-- The actual residue projections commute with every morphism over the source base. -/
@[reassoc]
lemma residueι_naturality {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) :
    ((residuePullback φ).map f).left ≫ residueι φ X = residueι φ Y ≫ f.left := by
  dsimp [residuePullback, residueι, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- The coefficient map from actual residue pullback and pushforward composition. -/
def residueCoefficient {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) :
    residueModule φ X ⟶ (Scheme.Modules.pushforward f.left).obj (residueModule φ Y) :=
  (Scheme.Modules.pushforward (residueι φ X)).map
      (unitToPushforwardUnit ((residuePullback φ).map f).left) ≫
    (Scheme.Modules.pushforwardComp ((residuePullback φ).map f).left
      (residueι φ X)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (residueι_naturality φ f)).hom.app _ ≫
    (Scheme.Modules.pushforwardComp (residueι φ Y) f.left).inv.app _

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
