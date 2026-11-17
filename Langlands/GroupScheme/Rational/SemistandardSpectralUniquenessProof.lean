import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof

/-! # Uniqueness of intrinsic semistandard triples from their parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SemistandardSpectralIndex

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G}

/-- In a fixed maximal split torus, equality of dynamic parabolics identifies
the entire intrinsic triple on every test scheme. -/
theorem ofCocharacter_eq_of_parabolic_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ζ eta : cocharacterLattice T)
    (hP : Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)) :
    ofCocharacter (i := i) hG ζ = ofCocharacter hG eta := by
  let := hG.isAffineHom
  let := hG.smooth
  have hnonneg : ∀ α ∈ relativeRoots i,
      0 ≤ latticePairing T α ζ ↔ 0 ≤ latticePairing T α eta := by
    intro α hα
    exact ⟨RelativeRoot.nonnegative_rootSupport_of_parabolic_le
        hi.isSplitSubtorus.1 i ζ eta (le_of_eq hP) α hα,
      RelativeRoot.nonnegative_rootSupport_of_parabolic_le
        hi.isSplitSubtorus.1 i eta ζ (le_of_eq hP.symm) α hα⟩
  obtain ⟨_, hM, hU⟩ := relativeRootSignsDetermineDynamic k G hG T i hi ζ eta (by
    intro α hα
    have hpos := hnonneg α hα
    have hneg := hnonneg (-α) (relativeRootNegation k G hG T i hi α hα)
    simp only [map_neg, LinearMap.neg_apply, neg_nonneg] at hneg
    exact ⟨hpos, by omega, by omega⟩)
  exact ofCocharacter_eq hG ζ eta hP hM hU

end SemistandardSpectralIndex

/-- Exact fixed-torus dynamic realization reduces intrinsic uniqueness to
the root-sign rigidity of dynamic parabolics. -/
theorem semistandardSpectralUniqueness_of_dynamicCoverage
    (hcoverage : SemistandardSpectralDynamicCoverageStatement.{u}) :
    SemistandardSpectralUniquenessStatement.{u} := by
  intro k _ G hG T i hi p q hpq
  obtain ⟨ζ, rfl⟩ := hcoverage k G hG T i hi p
  obtain ⟨eta, rfl⟩ := hcoverage k G hG T i hi q
  exact SemistandardSpectralIndex.ofCocharacter_eq_of_parabolic_eq hG hi ζ eta
    (congrArg Subtype.val hpq)

/-- The actual parabolic determines the distinguished Levi containing the
fixed maximal split torus and the geometric unipotent radical. -/
theorem semistandardSpectralUniqueness :
    SemistandardSpectralUniquenessStatement.{u} :=
  semistandardSpectralUniqueness_of_dynamicCoverage semistandardSpectralDynamicCoverage

end Langlands.GroupScheme
