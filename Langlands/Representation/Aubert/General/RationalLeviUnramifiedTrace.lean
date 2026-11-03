import Langlands.Representation.Aubert.General.UnramifiedInducedTrace
import Langlands.Representation.Aubert.General.RationalLeviCharacterDensity

/-! # Actual rational Levi norms in normalized induced distribution families -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology Plancherel
open HarmonicAnalysis MeasureTheory _root_.Topology

variable {F : Type u} [Field F] [TopologicalSpace F]
  [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance instRationalLeviUnramifiedTrace1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance instRationalLeviUnramifiedTrace2 :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instRationalLeviUnramifiedTrace3 : IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instRationalLeviUnramifiedTrace4 : TopologicalSpace (rationalPoints G) := pointTopology
local instance instRationalLeviUnramifiedTrace5 :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν I)).X

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)]
  [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  {P U : Subgroup (rationalPoints G)}
  (h : IsSemidirectDecomposition P (levi i ν I) U)
  (hU : IsClosed (U : Set (rationalPoints G))) (hproj : Continuous h.projection)
  (μG : Measure (rationalPoints G))
  [IsFiniteMeasureOnCompacts μG] [Measure.IsMulLeftInvariant μG]
  [CompactSpace (Induction.LeftQuotient P)]

/-- The genuine normalized induced distribution for the full rational norm
family of the literal Levi, with induced admissibility derived from `hA`. -/
def rationalLeviUnramifiedInductionDistribution
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible)
    (χ : unramifiedCharacters (leviRationalNormCharacters i ν I)) :
    Distribution (rationalPoints G) :=
  normalizedUnramifiedInductionDistribution h hU hproj μG
    (leviRationalNormCharacters i ν I) A hA χ

variable (hP : IsClosed (P : Set (rationalPoints G)))

/-- The finite coefficient function is chosen before every character. All norm
continuity premises are discharged by the actual full rational norm family. -/
theorem rationalLeviUnramifiedInductionDistribution_eval
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible)
    (χ : unramifiedCharacters (leviRationalNormCharacters i ν I))
    (f : SchwartzBruhat (rationalPoints G)) :
    rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA χ f =
      Finsupp.linearCombination ℂ (fun p : P => (χ.val (h.projection p) : ℂ))
        (normalizedInductionTwistCoefficients h hU hproj μG hP A hA f) :=
  normalizedUnramifiedInductionDistribution_eval h hU hproj μG hP
    (leviRationalNormCharacters i ν I) (continuous_leviRationalNormCharacters i ν I)
    A hA χ f

include hP in
/-- Scalar continuity in the actual compact-open unramified character topology. -/
theorem continuous_rationalLeviUnramifiedInductionDistribution
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible)
    (f : SchwartzBruhat (rationalPoints G)) :
    Continuous (fun χ : unramifiedCharacters (leviRationalNormCharacters i ν I) =>
      rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA χ f) :=
  continuous_normalizedUnramifiedInductionDistribution h hU hproj μG hP
    (leviRationalNormCharacters i ν I) (continuous_leviRationalNormCharacters i ν I)
    A hA f

/-- In the actual finite coordinates, the same finite coefficients evaluate
against Laurent monomials in the actual valuation-image lattice. -/
theorem rationalLeviUnramifiedInductionDistribution_coordinates_eval
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible)
    (z : Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I))) → ℂˣ)
    (f : SchwartzBruhat (rationalPoints G)) :
    rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA
        ((leviRationalUnramifiedCharacterCoordinates i ν I hL).symm z) f =
      Finsupp.linearCombination ℂ (fun p : P =>
        ((∏ j, z j ^ ((rationalReductiveValuationBasis
          (Standard.leviScheme i ν (rootSet i ν I)) hL).repr
            (Additive.ofMul (rationalValuationImageProjection
              (Standard.leviScheme i ν (rootSet i ν I))
                ((leviRationalPointHomeomorph i ν I).symm (h.projection p)))) j)) : ℂ))
        (normalizedInductionTwistCoefficients h hU hproj μG hP A hA f) := by
  rw [rationalLeviUnramifiedInductionDistribution_eval i ν I h hU hproj μG hP]
  apply congrArg (fun a : P → ℂ => Finsupp.linearCombination ℂ a
    (normalizedInductionTwistCoefficients h hU hproj μG hP A hA f))
  funext p
  simpa only [Units.coe_prod, Units.val_zpow_eq_zpow_val] using
    congrArg (fun a : ℂˣ => (a : ℂ))
      (leviRationalUnramifiedCharacterCoordinates_symm_apply i ν I hL z (h.projection p))

include hP in
/-- The genuine distribution values are also continuous in the published
finite coordinates of the same actual Levi representative. -/
theorem continuous_rationalLeviUnramifiedInductionDistribution_coordinates
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible)
    (f : SchwartzBruhat (rationalPoints G)) :
    Continuous (fun z : Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I))) → ℂˣ =>
      rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA
        ((leviRationalUnramifiedCharacterCoordinates i ν I hL).symm z) f) :=
  (continuous_rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG hP A hA f).comp
    (leviRationalUnramifiedCharacterCoordinates i ν I hL).symm.continuous

include hP in
/-- An explicitly supplied comparison on a nonzero actual coordinate principal
open extends to all characters for two decompositions sharing the literal Levi. -/
theorem rationalLeviUnramifiedInductionDistribution_eq_of_principalOpen
    {Q N : Subgroup (rationalPoints G)}
    (h' : IsSemidirectDecomposition Q (levi i ν I) N)
    (hN : IsClosed (N : Set (rationalPoints G))) (hproj' : Continuous h'.projection)
    (hQ : IsClosed (Q : Set (rationalPoints G))) [CompactSpace (Induction.LeftQuotient Q)]
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible)
    (B : SmoothRep.{0, u, w} ℂ (levi i ν I)) (hB : B.IsAdmissible)
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ)
    (hp : p ≠ 0)
    (hEq : ∀ χ ∈ leviUnramifiedPrincipalOpen i ν I hL p,
      rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA χ =
        rationalLeviUnramifiedInductionDistribution i ν I h' hN hproj' μG B hB χ) :
    ∀ χ, rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA χ =
      rationalLeviUnramifiedInductionDistribution i ν I h' hN hproj' μG B hB χ :=
  normalizedUnramifiedInductionDistribution_eq_of_dense h hU hproj μG hP
    (leviRationalNormCharacters i ν I) (continuous_leviRationalNormCharacters i ν I)
    h' hN hproj' hQ A hA B hB (leviUnramifiedPrincipalOpen i ν I hL p)
    (dense_leviUnramifiedPrincipalOpen i ν I hL p hp) hEq

end Langlands.Aubert.General.RationalPointFamily
