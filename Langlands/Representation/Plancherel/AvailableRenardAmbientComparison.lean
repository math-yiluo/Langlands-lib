import Langlands.Representation.Plancherel.RenardCartanAlgebraicComparison
import Langlands.Representation.Plancherel.RenardParahoricCompactTransport
import Langlands.BruhatTits.Cartan.AvailableCartanProof
import Langlands.BruhatTits.Iwasawa.AvailableProof
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality

/-! # The ambient Renard Cartan comparison on locally available KP data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.Plancherel.RenardCartan

/-- The ambient geometric and lattice clauses of the Renard comparison, using
only availability for this field and group and the original special vertex. -/
theorem availableSpecialCompactRenardComparison
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsAvailableFor F G hG →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          SpecialCompactRenardComparison B.apartment x ν
            B.centralizer.j B.centralizer.s B.centralizer.bijective := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx
  let B := (𝔅.datum F G hG).base
  let : B.normalizerZero.Normal := B.normal_normalizerZero
  have hcartan := Langlands.BruhatTits.Cartan.availableCartan F G hG 𝔅 h𝔅 ν hν x hx
  have hiwasawa :=
    (Langlands.BruhatTits.Iwasawa.availableIwasawa F G hG 𝔅 h𝔅 ν hν).1 x hx
  exact ⟨specialCompactCartanComparison_of_parahoric B ν x hcartan
      hiwasawa.2.1 hiwasawa.2.2.2.1,
    dominantLattice_of_maximalSplitTorus B.i B.isMaximalSplitTorus ν
      B.centralizer.s B.centralizer.bijective⟩

/-- The actual valuation chamber parametrizes double cosets for the original
special compact subgroup on locally available data. -/
def availableSpecialCompactChamberEquiv
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (𝔅 : KPBuildingAssignment.{u}) (_ : 𝔅.IsAvailableFor F G hG),
      let B := (𝔅.datum F G hG).base
      ∀ (ν : cocharacterLattice B.S) (_ : IsGenericCocharacter B.i ν)
        (x : B.Apartment) (_ : B.apartment.IsSpecialApartmentVertex x),
        Langlands.BruhatTits.Cartan.dominantValuationImage B.i ν
            B.centralizer.s B.centralizer.bijective ≃
          DoubleCoset.Quotient
            (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))
            (B.apartment.specialCompactSubgroup x) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx
  exact dominantChamberDoubleCosetEquiv _ x ν _ _ _
    (availableSpecialCompactRenardComparison F G hG 𝔅 h𝔅 ν hν x hx).1

end Langlands.Plancherel.RenardCartan
