import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement

/-! # Fundamental representations from integral coroot generation and highest weights -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The fundamental character supplied by the integral simple-coroot basis is
dominant for the same supplied base. -/
theorem fundamentalWeightBasis_isDominant (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (a : p.base.support) :
    p.IsDominantWeight
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a) := by
  classical
  intro b
  rw [Langlands.RootDatum.fundamentalWeightBasis_pairing]
  split_ifs <;> norm_num

/-- Package an actual highest-weight representation at the integral dual basis
character as a fundamental representation of the original supplied pinning. -/
def fundamentalRepresentationOfHighestWeight (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (a : p.base.support) {n : ℕ} (ρ : MatrixRepresentation G (Fin n))
    (hρ : p.IsHighestWeight ρ
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a)) :
    p.FundamentalRepresentation a where
  dimension := n
  representation := ρ
  highestWeight :=
    Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a
  isFundamentalWeight := by
    classical
    intro b
    exact Langlands.RootDatum.fundamentalWeightBasis_pairing
      p.rootDatum p.base hspan a b
  isHighestWeight := hρ

end SplitPinning

/-- Integral coroot generation and general dominant highest-weight existence
together imply the exact fundamental-representation proposition. -/
theorem splitFundamentalRepresentationsExist_of_corootSpan_of_highestWeight
    (hcoroot : SplitSimplyConnectedCorootSpanStatement.{u})
    (hhighest : SplitDominantHighestWeightRepresentationsExistStatement.{u}) :
    SplitFundamentalRepresentationsExistStatement.{u} := by
  classical
  intro k _ _ G _ p hG a
  have hspan : p.rootDatum.corootSpan ℤ = ⊤ :=
    hcoroot k G hG p.torus p.isSplitTorus p.inclusion p.isMaximalTorus
      p.rootIndex p.rootDatum p.isRootDatum p.isReduced
  obtain ⟨n, ρ, hρ⟩ :=
    hhighest k G p
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a)
      (p.fundamentalWeightBasis_isDominant hspan a)
  exact ⟨p.fundamentalRepresentationOfHighestWeight hspan a ρ hρ⟩

end Langlands.GroupScheme
