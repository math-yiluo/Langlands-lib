import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-!
# Iwasawa decomposition on available corrected Bruhat–Tits data

Both product orders of KP Theorem 5.3.4, for every actual parabolic and every special
vertex, with the actual parahoric and the same compact stabilizer. This is a statement
target conditional on the full corrected Definition 4.1.26, not an existence assertion.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.BruhatTits.Iwasawa

/-- KP Theorem 5.3.4 and its special maximal compact consequence on data satisfying
the full corrected KP Definition 4.1.26.

The first clause uses every special apartment vertex and the literal `B.parahoricAt x`.
The second uses every special vertex of the whole reduced building and every actual
parahoric at that point, in the published sense `B.IsParahoricAt y Q`.
Both clauses conclude the inclusion into the compact stabilizer, both product orders
for the parahoric and that same stabilizer, and compact-open maximality of the latter.
All six actual-parabolic families share each fixed subgroup. -/
def AvailableIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsAvailableFor F G hG →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        (∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          ParabolicPointProductFamily B.i ν (B.parahoricAt x) ∧
            B.parahoricAt x ≤ B.apartment.specialCompactSubgroup x ∧
            ParabolicPointProductFamily B.i ν (B.apartment.specialCompactSubgroup x) ∧
            IsCompactOpenMaximal F (B.apartment.specialCompactSubgroup x)) ∧
        ∀ y : B.ReducedBuilding, B.IsSpecialPoint y → B.IsVertex y →
          ∀ Q : Subgroup (rationalPoints G), B.IsParahoricAt y Q →
            ParabolicPointProductFamily B.i ν Q ∧
              Q ≤ B.compactStabilizer y ∧
              ParabolicPointProductFamily B.i ν (B.compactStabilizer y) ∧
              IsCompactOpenMaximal F (B.compactStabilizer y)

end Langlands.BruhatTits.Iwasawa
