import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# The simultaneous basis at every special vertex of valid corrected KP data

The compact properties, geometric standard-Levi inheritance and simultaneous
normal compact-open basis use the same datum, torus, cocharacter, vertex and
geometric compact stabilizer. This supplied-data target is separate from the
general existence targets and proves none of them.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- Renard V.5.2(i)--(iv), together with the compact and geometric Levi properties
of V.5.1, at every special apartment vertex of one valid corrected KP assignment.

`IsValid` supplies the full corrected Definition 4.1.26 for every connected
reductive group, including each actual standard Levi once its connected
reductivity is established. The Levi restriction and exact compact-preimage
equality remain conclusions. No equality is imposed between the ambient torus
and the independently chosen torus of the assignment's Levi datum. -/
def AvailableSimultaneousStandardBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
      let D := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice D.S, IsGenericCocharacter D.i ν →
        ∀ x : D.Apartment, D.apartment.IsSpecialApartmentVertex x →
          SpecialCompactProperties F D.i ν (D.apartment.specialCompactSubgroup x) ∧
            SpecialLeviInheritance F D.isMaximalSplitTorus ν D.apartment x ∧
            SimultaneousStandardBasisAt D.i ν (D.apartment.specialCompactSubgroup x)

end Langlands.BruhatTits.SpecialCompact
