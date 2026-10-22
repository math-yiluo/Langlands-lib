import Langlands.Cohomology.EquivariantDerivedSections
import Langlands.Cohomology.TopologicalDerivedSections
import Langlands.Cohomology.DerivedComparison
import Langlands.Sheaf.Equivariant.Induction
import Langlands.Sheaf.Equivariant.Exact

/-!
# Derived equivariant sections and cohomology of the underlying sheaf

The module underlying a derived equivariant section representation is the
ordinary sheaf cohomology of the underlying sheaf, for global and for
compactly supported sections.
-/

noncomputable section

namespace Langlands.Cohomology.EquivariantDerivedComparison

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The module underlying the global section representation is the ordinary
global section module of the underlying sheaf. -/
def globalSectionsForgetIso :
    sectionRepresentation R G X ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        Langlands.Sheaf.CompactSupport.globalSections (X := TopCat.of X) (R := R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The module underlying degree `q` derived equivariant global sections is
degree `q` ordinary cohomology of the underlying sheaf. -/
def globalDerivedForgetIso (q : ℕ) :
    EquivariantDerivedSections.globalDerived R G X q ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        TopologicalDerivedSections.ordinaryCohomology (TopCat.of X) R q :=
  DerivedComparison.rightDerivedCompIso (sectionRepresentation R G X)
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) (toSheaf G X (ModuleCat.{u} R))
    (Langlands.Sheaf.CompactSupport.globalSections (X := TopCat.of X) (R := R))
    (globalSectionsForgetIso R G X) q

/-- The module underlying degree `q` derived equivariant compactly supported
sections is degree `q` compactly supported cohomology of the underlying
sheaf. -/
def compactDerivedForgetIso (q : ℕ) :
    EquivariantDerivedSections.compactDerived R G X q ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        TopologicalDerivedSections.compactCohomology (TopCat.of X) R q :=
  DerivedComparison.rightDerivedCompIso (CompactSections.functor R G X)
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) (toSheaf G X (ModuleCat.{u} R))
    (Langlands.Sheaf.CompactSupport.functor (X := TopCat.of X) (R := R))
    (EquivariantDerivedSections.compactSectionsForgetIso R G X) q

end Langlands.Cohomology.EquivariantDerivedComparison
