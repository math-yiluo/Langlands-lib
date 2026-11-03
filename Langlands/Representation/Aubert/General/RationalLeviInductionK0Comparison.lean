import Langlands.Representation.Aubert.General.RationalLeviUnramifiedTrace
import Langlands.Representation.Aubert.General.UnramifiedInducedK0Comparison
import Langlands.Representation.Aubert.General.AlternatingOperator

/-! # Actual rational Levi principal-open comparisons in exact K0 -/

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
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance : IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance : TopologicalSpace (rationalPoints G) := pointTopology
local instance :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν I)).X


variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)]
  [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  {P U : Subgroup (rationalPoints G)}
  (h : IsSemidirectDecomposition P (levi i ν I) U)
  (hU : IsClosed (U : Set (rationalPoints G)))
  (μG : Measure (rationalPoints G)) [μG.IsHaarMeasure] [μG.Regular]

/-- The genuine character of normalized induction as an integer-linear map on
exact finite-length K0 of the literal rational Levi. -/
def rationalLeviInductionK0Distribution
    (hAdm : ∀ (C : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      C.HasFiniteLength → C.IsAdmissible)
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} h hU)) :
    FiniteLengthGrothendieckGroup.{0, u, max u v} ℂ (levi i ν I) →ₗ[ℤ]
      Distribution (rationalPoints G) :=
  (Character.exactK0DistributionCharacter μG hAdm).comp (inductionK0 h hU hl hx)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Its value on every actual finite-length object is the genuine distribution
of its normalized induction. -/
theorem rationalLeviInductionK0Distribution_ofRepresentation
    (hAdm : ∀ (C : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      C.HasFiniteLength → C.IsAdmissible)
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} h hU))
    (A : SmoothRep.{0, u, max u v} ℂ (levi i ν I)) (hA : A.HasFiniteLength) :
    rationalLeviInductionK0Distribution i ν I h hU μG hAdm hl hx
        (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      Character.distribution μG ((normalizedInductionFunctor h hU).obj A).representation
        (hAdm _ (hl A hA)) := by
  simp only [rationalLeviInductionK0Distribution, LinearMap.comp_apply,
    inductionK0_ofRepresentation, Character.exactK0DistributionCharacter_ofRepresentation]

variable (hproj : Continuous h.projection)
  [CompactSpace (Induction.LeftQuotient P)]
  (hP : IsClosed (P : Set (rationalPoints G)))

include hP in
/-- An actual nonzero coordinate principal-open distribution comparison yields
equality of the original normalized induced exact classes. -/
theorem rationalLeviInductionClass_eq_of_principalOpen
    (hAdm : ∀ (C : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      C.HasFiniteLength → C.IsAdmissible)
    {Q N : Subgroup (rationalPoints G)}
    (h' : IsSemidirectDecomposition Q (levi i ν I) N)
    (hN : IsClosed (N : Set (rationalPoints G))) (hproj' : Continuous h'.projection)
    (hQ : IsClosed (Q : Set (rationalPoints G))) [CompactSpace (Induction.LeftQuotient Q)]
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (A B : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hA : A.IsAdmissible) (hB : B.IsAdmissible)
    (hAfl : ((normalizedInductionFunctor h hU).obj A).HasFiniteLength)
    (hBfl : ((normalizedInductionFunctor h' hN).obj B).HasFiniteLength)
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ)
    (hp : p ≠ 0)
    (hEq : ∀ χ ∈ leviUnramifiedPrincipalOpen i ν I hL p,
      rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG A hA χ =
        rationalLeviUnramifiedInductionDistribution i ν I h' hN hproj' μG B hB χ) :
    FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor h hU).obj A) hAfl =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor h' hN).obj B) hBfl := by
  exact normalizedInductionClass_eq_of_dense (ν := leviRationalNormCharacters i ν I)
    h hU hproj μG hP hAdm (continuous_leviRationalNormCharacters i ν I)
    h' hN hproj' hQ A B hA hB hAfl hBfl (leviUnramifiedPrincipalOpen i ν I hL p)
    (dense_leviUnramifiedPrincipalOpen i ν I hL p hp) hEq

include hP in
/-- A possibly different nonzero polynomial for each actual finite-length
coefficient suffices to identify the entire two induction maps on exact K0. -/
theorem rationalLeviInductionK0_eq_of_principalOpen
    (hAdm : ∀ (C : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      C.HasFiniteLength → C.IsAdmissible)
    (hAdmL : ∀ (A : SmoothRep.{0, u, max u v} ℂ (levi i ν I)),
      A.HasFiniteLength → A.IsAdmissible)
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} h hU))
    {Q N : Subgroup (rationalPoints G)}
    (h' : IsSemidirectDecomposition Q (levi i ν I) N)
    (hN : IsClosed (N : Set (rationalPoints G))) (hproj' : Continuous h'.projection)
    (hQ : IsClosed (Q : Set (rationalPoints G))) [CompactSpace (Induction.LeftQuotient Q)]
    (hl' : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} h' hN))
    (hx' : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} h' hN))
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (hEq : ∀ σ : FiniteLengthObject.{0, u, max u v} ℂ (levi i ν I),
      ∃ p : MvPolynomial
          (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ,
        p ≠ 0 ∧ ∀ χ ∈ leviUnramifiedPrincipalOpen i ν I hL p,
          rationalLeviUnramifiedInductionDistribution i ν I h hU hproj μG
              σ.val (hAdmL σ.val σ.property) χ =
            rationalLeviUnramifiedInductionDistribution i ν I h' hN hproj' μG
              σ.val (hAdmL σ.val σ.property) χ) :
    inductionK0 h hU hl hx = inductionK0 h' hN hl' hx' := by
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (levi i ν I)
  intro σ
  change (inductionK0 h hU hl hx)
      (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property) =
    (inductionK0 h' hN hl' hx')
      (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property)
  rw [inductionK0_ofRepresentation, inductionK0_ofRepresentation]
  obtain ⟨p, hp, hσ⟩ := hEq σ
  exact rationalLeviInductionClass_eq_of_principalOpen i ν I h hU μG hproj hP hAdm
    h' hN hproj' hQ hL σ.val σ.val (hAdmL σ.val σ.property)
    (hAdmL σ.val σ.property) (hl σ.val σ.property) (hl' σ.val σ.property) p hp hσ

end Langlands.Aubert.General.RationalPointFamily
