import Langlands.Geometry.Building.KPLieFiltrationOnBuilding
import Langlands.Geometry.Building.KPOptimalPoints
import Langlands.Geometry.Building.KPNilpotentCoset
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Mathlib.RingTheory.Finiteness.Basic

/-!
# A degenerate Lie coset lies in a deeper lattice (KP Proposition 13.6.7, first assertion)

Kaletha–Prasad, Proposition 13.6.7, first assertion, for supplied relative affine-root Lie data
on supplied building data. The lattices at points of the reduced building are the published
`lieFiltrationOnBuilding`, glued from the apartment lattices under `IsAdjointCompatible`.
The first target puts the coset in a deeper lattice at some point of the reduced building. The
second also makes that point optimal (KP Definition 13.4.2), which needs a nonempty set of affine
roots. The second assertion of 13.6.7 (instability under `G_x`) is not stated here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open ParahoricBuildingData.LieFiltrationData

/-- Let `L` be periodic and compatible with the adjoint action, on building data satisfying the
apartment axioms. Let `X ∈ 𝔤_{x,r}` represent a degenerate coset `X + 𝔤_{x,r+}`, and suppose that
`𝔤_{x,r+}` is finitely generated over `𝒪[F]`. Then some point `y` of the reduced building and some
`s > r` satisfy `X + 𝔤_{x,r+} ⊆ 𝔤_{y,s}`. -/
def DegenerateLieCosetInDeeperLatticeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (L : P.LieFiltrationData) (hL : L.IsAdjointCompatible), L.IsPeriodic →
    ∀ (x : P.Apartment) (r : ℝ), (L.lieFiltrationPlusReal x r).FG →
    ∀ X ∈ L.lieFiltrationReal x r, IsDegenerateLieCoset (L.lieFiltrationPlusReal x r) X →
      ∃ (y : P.ReducedBuilding) (s : ℝ), r < s ∧
        ∀ Y : GenericLie 𝒪[F] G, Y - X ∈ L.lieFiltrationPlusReal x r →
          Y ∈ lieFiltrationOnBuilding hL y s

/-- KP Proposition 13.6.7, first assertion, with the hypotheses of
`DegenerateLieCosetInDeeperLatticeStatement` and a nonempty set of affine roots: the point `y`
can be chosen optimal (`ValuationBuildingData.IsOptimalPoint`, KP Definition 13.4.2). Without
affine roots there are no optimal points, while the coset `𝔤_{x,r+}` of `0` is degenerate. -/
def DegenerateLieCosetInOptimalLatticeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms → P.affineRoots.Nonempty →
    ∀ (L : P.LieFiltrationData) (hL : L.IsAdjointCompatible), L.IsPeriodic →
    ∀ (x : P.Apartment) (r : ℝ), (L.lieFiltrationPlusReal x r).FG →
    ∀ X ∈ L.lieFiltrationReal x r, IsDegenerateLieCoset (L.lieFiltrationPlusReal x r) X →
      ∃ (y : P.ReducedBuilding) (s : ℝ), P.IsOptimalPoint y ∧ r < s ∧
        ∀ Y : GenericLie 𝒪[F] G, Y - X ∈ L.lieFiltrationPlusReal x r →
          Y ∈ lieFiltrationOnBuilding hL y s

end Langlands.Geometry.Building
