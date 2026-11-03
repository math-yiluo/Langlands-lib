import Langlands.Representation.Plancherel.CharacterTorusDensity
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates

/-! # Principal open density on actual rational unramified characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem rationalDensity_isAffine (hG : GroupScheme.IsConnectedReductive G) :
    IsAffine G.X.left := by
  have := hG.isAffineHom
  exact isAffine_of_isAffineHom G.X.hom

/-- A polynomial principal open locus in the published finite coordinates on actual
unramified characters, with their inherited compact-open topology. -/
def rationalUnramifiedPrincipalOpen (hG : GroupScheme.IsConnectedReductive G)
    (p : MvPolynomial (Fin (rationalImageRank G)) ℂ) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    Set (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) := by
  letI : IsAffine G.X.left := rationalDensity_isAffine G hG
  letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  exact (rationalCanonicalUnramifiedCharacterCoordinates G hG) ⁻¹' complexTorusPrincipalOpen p

/-- Membership is precisely nonvanishing at the actual character's canonical coordinates. -/
theorem mem_rationalUnramifiedPrincipalOpen (hG : GroupScheme.IsConnectedReductive G)
    (p : MvPolynomial (Fin (rationalImageRank G)) ℂ) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul),
      chi ∈ rationalUnramifiedPrincipalOpen G hG p ↔
        MvPolynomial.eval
          (fun i => (rationalCanonicalUnramifiedCharacterCoordinates G hG chi i : ℂ)) p ≠ 0 := by
  let : IsAffine G.X.left := rationalDensity_isAffine G hG
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro chi
  exact Iff.rfl

/-- The actual unramified principal open locus is open in its compact-open topology. -/
theorem isOpen_rationalUnramifiedPrincipalOpen (hG : GroupScheme.IsConnectedReductive G)
    (p : MvPolynomial (Fin (rationalImageRank G)) ℂ) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    IsOpen (rationalUnramifiedPrincipalOpen G hG p) := by
  let : IsAffine G.X.left := rationalDensity_isAffine G hG
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  exact isOpen_complexTorusPrincipalOpen_preimage
    (rationalCanonicalUnramifiedCharacterCoordinates G hG).toHomeomorph p

/-- Every nonzero polynomial defines a dense locus of actual unramified characters. -/
theorem dense_rationalUnramifiedPrincipalOpen (hG : GroupScheme.IsConnectedReductive G)
    (p : MvPolynomial (Fin (rationalImageRank G)) ℂ) (hp : p ≠ 0) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    Dense (rationalUnramifiedPrincipalOpen G hG p) := by
  let : IsAffine G.X.left := rationalDensity_isAffine G hG
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  exact dense_complexTorusPrincipalOpen_preimage
    (rationalCanonicalUnramifiedCharacterCoordinates G hG).toHomeomorph p hp

/-- Finite intersections of these actual principal open loci correspond to products. -/
theorem rationalUnramifiedPrincipalOpen_finsetProd (hG : GroupScheme.IsConnectedReductive G)
    {κ : Type v} (s : Finset κ)
    (p : κ → MvPolynomial (Fin (rationalImageRank G)) ℂ) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    rationalUnramifiedPrincipalOpen G hG (∏ j ∈ s, p j) =
      ⋂ j ∈ s, rationalUnramifiedPrincipalOpen G hG (p j) := by
  let : IsAffine G.X.left := rationalDensity_isAffine G hG
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  simp only [rationalUnramifiedPrincipalOpen, complexTorusPrincipalOpen_finsetProd,
    preimage_iInter]

/-- Finitely many nonzero polynomial conditions give a dense actual character family. -/
theorem dense_iInter_rationalUnramifiedPrincipalOpen (hG : GroupScheme.IsConnectedReductive G)
    {κ : Type v} (s : Finset κ)
    (p : κ → MvPolynomial (Fin (rationalImageRank G)) ℂ) (hp : ∀ j ∈ s, p j ≠ 0) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    Dense (⋂ j ∈ s, rationalUnramifiedPrincipalOpen G hG (p j)) := by
  let : IsAffine G.X.left := rationalDensity_isAffine G hG
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  rw [← rationalUnramifiedPrincipalOpen_finsetProd G hG s p]
  exact dense_rationalUnramifiedPrincipalOpen G hG _ (Finset.prod_ne_zero_iff.mpr hp)

/-- A family containing one nonzero canonical-coordinate principal open locus is dense. -/
theorem dense_of_rationalUnramifiedPrincipalOpen_subset (hG : GroupScheme.IsConnectedReductive G)
    (p : MvPolynomial (Fin (rationalImageRank G)) ℂ) (hp : p ≠ 0) :
    letI : IsAffine G.X.left := rationalDensity_isAffine G hG
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ {S : Set (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))},
      rationalUnramifiedPrincipalOpen G hG p ⊆ S → Dense S := by
  let : IsAffine G.X.left := rationalDensity_isAffine G hG
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro S hS
  exact (dense_rationalUnramifiedPrincipalOpen G hG p hp).mono hS

end Langlands.Plancherel
