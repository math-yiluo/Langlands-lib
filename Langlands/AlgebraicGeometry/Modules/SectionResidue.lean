import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Pullback of sections and values on residue-field fibres -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

/-- The pulled-back section as a map out of the structure module. -/
def pullbackSectionHom (s : GlobalSections M) :
    structureModule Y ⟶ (Scheme.Modules.pullback f).obj M :=
  (Langlands.Scheme.Modules.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map (sectionHom M s)

/-- Pullback of a global section, obtained by evaluating its module morphism at one. -/
def pullbackSection (s : GlobalSections M) :
    GlobalSections ((Scheme.Modules.pullback f).obj M) :=
  (pullbackSectionHom f M s).app ⊤ (1 : Γ(Y, ⊤))

/-- The actual module sheaf on the spectrum of the residue field at a point. -/
def residueFibre (x : X) : (Spec (X.residueField x)).Modules :=
  (Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M

/-- The value of a global section as a section on its residue-field fibre. -/
def residueSection (s : GlobalSections M) (x : X) :
    GlobalSections (residueFibre M x) :=
  pullbackSection (X.fromSpecResidueField x) M s

/-- Nonvanishing of the actual section on the residue-field fibre. -/
def NonvanishingAt (s : GlobalSections M) (x : X) : Prop :=
  residueSection M s x ≠ 0

/-- The set of points where a section has nonzero residue-field value. -/
def nonvanishingLocus (s : GlobalSections M) : Set X :=
  {x | NonvanishingAt M s x}

lemma mem_nonvanishingLocus (s : GlobalSections M) (x : X) :
    x ∈ nonvanishingLocus M s ↔ residueSection M s x ≠ 0 :=
  Iff.rfl

end Langlands.SchemeModule
