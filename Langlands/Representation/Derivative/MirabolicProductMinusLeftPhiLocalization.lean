import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
import Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization

/-! The actual normalized left mixed product and its entire identity-orbit localization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  HarmonicAnalysis Induction Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)

/-- The full identity-orbit quotient with the actual ambient inverse-half
determinant normalization, naturally in both original smooth inputs. -/
def leftPhiNormalizedIdentityPiece :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  (leftPhiMackeyInput T k r ⋙
    orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
      (leftRepresentative k r F.Carrier 1) ⋙ leftPhiPlusKernelFunctor T k r ψ) ⋙
    (⟨Mirabolic.phiMinusCharacter T (k + r + 1),
      Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩ :
        SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier)).twistFunctor

private def leftPhiProductAssociationIso :
    letI := T.topology
    leftPhiProduct.{uF, uV} T ψ k (r + 1) ≅
      (T.leftMixedProductFunctor (k + 1) (r + 1) ⋙
        mirabolicRankCast T (totalRank_eq k r)) ⋙
          Mirabolic.phiMinus T ψ (k + r + 1) :=
  letI := T.topology
  (Functor.associator (T.leftMixedProductFunctor (k + 1) (r + 1))
    (mirabolicRankCast T (totalRank_eq k r))
    (Mirabolic.phiMinus T ψ (k + r + 1))).symm

set_option maxHeartbeats 800000 in
/-- Actual Phi-minus of the higher mixed product is the normalized full
identity-orbit localization. The map uses the published natural Mackey quotient. -/
def leftPhiProductIdentityIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    leftPhiProduct.{uF, uV} T ψ k (r + 1) ⋙ SmoothRep.toRep ≅
      leftPhiNormalizedIdentityPiece T ψ k r := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  let χ : SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier) :=
    ⟨Mirabolic.phiMinusCharacter T (k + r + 1),
      Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩
  let H := leftPhiMackeyInput.{uF, uV} T k r ⋙ SmoothRep.toRep ⋙
    compactInductionFunctor (leftInducing k r F.Carrier)
  let e₁ :
      ((T.leftMixedProductFunctor (k + 1) (r + 1) ⋙
        mirabolicRankCast T (totalRank_eq k r)) ⋙
          (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep)) ≅
        H ⋙ (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep) :=
    Functor.isoWhiskerRight (leftPhiHostInductionIso.{uF, uV} T k r)
      (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep)
  let e₂ : H ⋙ (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep) ≅
      (leftPhiMackeyInput T k r ⋙
        restrictedCompactInduction (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) ⋙ leftPhiPlusKernelFunctor T k r ψ) ⋙
        χ.twistFunctor :=
    Functor.isoWhiskerLeft H
      (Functor.isoWhiskerRight (phiMinusNormalizedKernelIso T ψ (k + r + 1)).symm
        SmoothRep.toRep)
  let e₃ := Functor.isoWhiskerRight
    (leftPhiMackeyLocalizedIso.{uF, uV} T k r ψ) χ.twistFunctor
  let e₀ := Functor.isoWhiskerRight (leftPhiProductAssociationIso.{uF, uV} T ψ k r)
    SmoothRep.toRep
  let a := Functor.associator
    (T.leftMixedProductFunctor (k + 1) (r + 1) ⋙ mirabolicRankCast T (totalRank_eq k r))
    (Mirabolic.phiMinus T ψ (k + r + 1)) SmoothRep.toRep
  let e := e₀ ≪≫ a ≪≫ e₁ ≪≫ e₂ ≪≫ e₃
  unfold leftPhiNormalizedIdentityPiece
  with_reducible exact e

end Langlands.Derivative.MirabolicProductMinus
