import Langlands.Representation.Plancherel.RationalImageLattice
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterTopology

/-! # Finite coordinates on actual unramified characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The same chosen image basis, with finiteness discharged by reductivity. -/
def rationalReductiveValuationBasis (hG : GroupScheme.IsConnectedReductive G) :
    Module.Basis (Fin (rationalImageRank G)) ℤ
      (Additive (rationalDiscreteValuationImage G)) := by
  letI := (GroupScheme.rationalCharacterLattice F G hG).2
  exact rationalImageBasis G

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem rationalReductive_isAffine (hG : GroupScheme.IsConnectedReductive G) :
    IsAffine G.X.left := by
  have := hG.isAffineHom
  exact isAffine_of_isAffineHom G.X.hom

/-- Finite complex coordinates on actual unramified characters in the canonical
rational-point topology. -/
def rationalCanonicalUnramifiedCharacterCoordinates
    (hG : GroupScheme.IsConnectedReductive G) :
    letI : IsAffine G.X.left := rationalReductive_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) ≃ₜ*
      (Fin (rationalImageRank G) → ℂˣ) := by
  letI : IsAffine G.X.left := rationalReductive_isAffine G hG
  letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  haveI := hG.smooth
  exact (rationalCanonicalImageUnramifiedContinuousEquiv G).symm.trans
    (rationalReductiveImageCharacterCoordinates G hG)

/-- Finite circle coordinates on the actual unitary unramified subgroup. -/
def rationalCanonicalUnitaryUnramifiedCharacterCoordinates
    (hG : GroupScheme.IsConnectedReductive G) :
    letI : IsAffine G.X.left := rationalReductive_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) ≃ₜ*
      (Fin (rationalImageRank G) → Circle) := by
  letI : IsAffine G.X.left := rationalReductive_isAffine G hG
  letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  haveI := hG.smooth
  exact (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G).symm.trans
    (rationalReductiveUnitaryImageCoordinates G hG)

/-- Reconstructing a tuple gives the corresponding Laurent monomial at every
actual rational point. -/
theorem rationalCanonicalUnramifiedCharacterCoordinates_symm_apply
    (hG : GroupScheme.IsConnectedReductive G)
    (c : Fin (rationalImageRank G) → ℂˣ) (g : GroupScheme.rationalPoints G) :
    ((rationalCanonicalUnramifiedCharacterCoordinates G hG).symm c).val g =
      ∏ i, c i ^ ((rationalReductiveValuationBasis G hG).repr
        (Additive.ofMul (rationalValuationImageProjection G g)) i) := by
  let _ := (GroupScheme.rationalCharacterLattice F G hG).2
  change rationalImageCharacterOfCoordinates G c (rationalValuationImageProjection G g) = _
  exact rationalImageCharacterOfCoordinates_apply G c _

/-- The unitary reconstruction has the same Laurent formula, with circle values
included in the complex numbers. -/
theorem rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply
    (hG : GroupScheme.IsConnectedReductive G)
    (c : Fin (rationalImageRank G) → Circle) (g : GroupScheme.rationalPoints G) :
    ((((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm c).val g :
      ℂˣ) : ℂ) =
      ((∏ i, c i ^ ((rationalReductiveValuationBasis G hG).repr
        (Additive.ofMul (rationalValuationImageProjection G g)) i) : Circle) : ℂ) := by
  let _ := (GroupScheme.rationalCharacterLattice F G hG).2
  change ((rationalImageCharacterOfCoordinates G c
    (rationalValuationImageProjection G g) : Circle) : ℂ) = _
  rw [rationalImageCharacterOfCoordinates_apply]
  rfl

/-- Forgetting unitary membership agrees with including each circle coordinate
in the complex units. -/
theorem rationalCanonicalUnitaryUnramifiedCharacterCoordinates_coe
    (hG : GroupScheme.IsConnectedReductive G)
    (chi :
      letI : IsAffine G.X.left := rationalReductive_isAffine G hG
      letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
      unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
    (i : Fin (rationalImageRank G)) :
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG chi i : ℂ) =
      ((rationalCanonicalUnramifiedCharacterCoordinates G hG
        ⟨chi.val, chi.property.1⟩ i : ℂˣ) : ℂ) := rfl

end Langlands.Plancherel
