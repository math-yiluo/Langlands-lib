import Langlands.Representation.Aubert.General.RationalLeviInductionK0Comparison
import Langlands.Representation.Aubert.General.ConjugateInduction
import Langlands.Representation.Aubert.General.ConjugateParabolicTopology

/-! # Rational principal-open comparison and actual conjugation on exact K0 -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Langlands.AlgebraicGeometry.PointTopology Plancherel
open HarmonicAnalysis MeasureTheory _root_.Topology

variable {F : Type u} [Field F] [TopologicalSpace F]
  [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I J : Finset (SimpleRoot i ν))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν J)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J)
local instance : IsAffine (Standard.leviScheme i ν (rootSet i ν J)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν J)).hom.hom.left
local instance : TopologicalSpace (rationalPoints G) := pointTopology
local instance :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν J)).X


variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)]
  [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  {P U Q V : Subgroup (rationalPoints G)}
  (hI : IsSemidirectDecomposition P (levi i ν I) U)
  (hJ : IsSemidirectDecomposition Q (levi i ν J) V)
  (g : rationalPoints G)
  (hIJ : ∀ x : rationalPoints G,
    x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I)
  (hU : IsClosed (U : Set (rationalPoints G)))
  (hV : IsClosed (V : Set (rationalPoints G)))
  (hprojI : Continuous hI.projection) (hprojJ : Continuous hJ.projection)
  (μG : Measure (rationalPoints G)) [μG.IsHaarMeasure] [μG.Regular]
  [CompactSpace (Induction.LeftQuotient P)] [CompactSpace (Induction.LeftQuotient Q)]

local instance : CompactSpace (Induction.LeftQuotient (conjugateSubgroup g P)) :=
  compactSpace_leftQuotient_conjugateSubgroup g P

/-- The actual locus comparing standard induction on the common literal Levi
with induction from the conjugate parabolic. -/
def rationalConjugateInductionComparisonLocus
    (A : SmoothRep.{0, u, v} ℂ (levi i ν J)) (hA : A.IsAdmissible) :
    Set (unramifiedCharacters (leviRationalNormCharacters i ν J)) :=
  {χ | rationalLeviUnramifiedInductionDistribution i ν J hJ hV hprojJ μG A hA χ =
    rationalLeviUnramifiedInductionDistribution i ν J
      (hI.conjugateWithLevi g hIJ) (isClosed_conjugateSubgroup g hU)
      (hI.continuous_conjugateWithLevi_projection hprojI g hIJ) μG A hA χ}

/-- An actual nonzero principal-open comparison on each finite-length object
implies the entire inverse-conjugation induction identity. -/
theorem inductionK0_comp_conjugationK0_of_rationalPrincipalOpen
    (hP : IsClosed (P : Set (rationalPoints G)))
    (hQ : IsClosed (Q : Set (rationalPoints G)))
    (hAdm : ∀ (C : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      C.HasFiniteLength → C.IsAdmissible)
    (hAdmJ : ∀ (A : SmoothRep.{0, u, max u v} ℂ (levi i ν J)),
      A.HasFiniteLength → A.IsAdmissible)
    (hlI : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} hI hU))
    (hxI : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} hI hU))
    (hlJ : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} hJ hV))
    (hxJ : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} hJ hV))
    (hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J)))
    (hEq : ∀ σ : FiniteLengthObject.{0, u, max u v} ℂ (levi i ν J),
      ∃ p : MvPolynomial
          (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν J)))) ℂ,
        p ≠ 0 ∧ leviUnramifiedPrincipalOpen i ν J hLJ p ⊆
          rationalConjugateInductionComparisonLocus i ν I J hI hJ g hIJ hU hV
            hprojI hprojJ μG σ.val (hAdmJ σ.val σ.property)) :
    (inductionK0 hJ hV hlJ hxJ).comp
        (conjugationK0.{u, max u v} g hIJ) = inductionK0 hI hU hlI hxI := by
  apply inductionK0_comp_conjugationK0_of_sameLevi
    hI hJ g hIJ hU hV hlI hxI hlJ hxJ
  change inductionK0 hJ hV hlJ hxJ =
    inductionK0 (hI.conjugateWithLevi g hIJ) (isClosed_conjugateSubgroup g hU)
      (conjugateInductionFunctor_preservesFiniteLength hI g hIJ hU hlI)
      (conjugateInductionFunctor_preservesShortExact hI g hIJ hU hxI)
  apply rationalLeviInductionK0_eq_of_principalOpen i ν J hJ hV μG hprojJ hQ
    hAdm hAdmJ hlJ hxJ (hI.conjugateWithLevi g hIJ)
    (isClosed_conjugateSubgroup g hU)
    (hI.continuous_conjugateWithLevi_projection hprojI g hIJ)
    (isClosed_conjugateSubgroup g hP)
    (conjugateInductionFunctor_preservesFiniteLength hI g hIJ hU hlI)
    (conjugateInductionFunctor_preservesShortExact hI g hIJ hU hxI) hLJ
  intro σ
  obtain ⟨p, hp, hσ⟩ := hEq σ
  exact ⟨p, hp, hσ⟩

end Langlands.Aubert.General.RationalPointFamily
