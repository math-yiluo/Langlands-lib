import Langlands.Representation.Exponents.CasselmanStandardTorusTests
import Langlands.Representation.Exponents.CasselmanUniverseLift

/-! # Sufficiency assembly for supplied actual standard presentations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- An actual represented parabolic, Levi, radical and component with a
compatible presentation at one specified standard index and the exact
matching radical point subgroup. This is supplied data, not an existence theorem. -/
structure StandardCasselmanPresentation
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) where
  P : GroupScheme (Spec (CommRingCat.of k))
  M : GroupScheme (Spec (CommRingCat.of k))
  U : GroupScheme (Spec (CommRingCat.of k))
  A : CommGroupScheme (Spec (CommRingCat.of k))
  p : P ⟶ G
  l : M ⟶ P
  r : U ⟶ P
  a : A.toGrp ⟶ M
  f : A ⟶ T
  compatible : (ParabolicRootPresentationData.mk T i ν
    (RationalPointFamily.rootSet i ν I) f).IsCompatible p l a
  radical : LeviSubgroup.IsGeometricUnipotentRadical r
  multiplication : IsIso (subgroupMultiplication l r)
  radical_points_eq : pointImage (r ≫ p) = RationalPointFamily.unipotent i ν I

namespace StandardCasselmanPresentation

variable {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {I : Finset (RationalPointFamily.SimpleRoot i ν)}
  (D : StandardCasselmanPresentation i ν I)

/-- The supplied standard data as the existing actual root presentation. -/
def rootPresentation : ParabolicRootPresentation D.p D.l D.a :=
  ⟨⟨T, i, ν, RationalPointFamily.rootSet i ν I, D.f⟩, D.compatible⟩

/-- Its compatible all-test Levi equality gives the exact literal point equality. -/
theorem levi_points_eq :
    pointImage (D.l ≫ D.p) = RationalPointFamily.levi i ν I :=
  congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
    D.compatible.levi_eq

end StandardCasselmanPresentation

section ConeCondition

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [T2Space k] [LocallyOfFiniteType G.X.hom]

local instance assemblyAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The all-represented-parabolic positive-cone condition appearing on the
right of the published Casselman criterion. No presentation existence is included. -/
def HasPositiveRepresentedJacquetExponents
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
    (pres : ParabolicRootPresentation p l a) (χ : rationalPoints A.toGrp →* ℂˣ),
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈ pres.positiveCone

/-- The all-represented cone condition supplies the strict standard full-center
test at every supplied matching standard presentation. -/
theorem strictStandardExponents_of_positiveRepresented
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (D : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν), StandardCasselmanPresentation i ν I)
    (h : ∀ I, IsSemidirectDecomposition (RationalPointFamily.parabolic i ν I)
      (RationalPointFamily.levi i ν I) (RationalPointFamily.unipotent i ν I))
    (hU : ∀ I, IsClosed (RationalPointFamily.unipotent i ν I : Set (rationalPoints G)))
    (hselected : ∀ I (t : rationalPoints T.toGrp)
      (z : Subgroup.center (RationalPointFamily.levi i ν I)),
      ((z : RationalPointFamily.levi i ν I) : rationalPoints G) = rationalPoints.map i t →
      ∀ α ∈ I, ValuativeRel.valuation k
        (RationalPointFamily.simpleRootPointValue i ν α t : k) = 1)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hcone : HasPositiveRepresentedJacquetExponents π)
    (I : Finset (RationalPointFamily.SimpleRoot i ν))
    (χ : Subgroup.center (RationalPointFamily.levi i ν I) →* ℂˣ)
    (hχ : IsCentralExponent ((Langlands.Aubert.General.jacquetFunctor
      (h I) (hU I)).obj π).representation χ) :
    RationalPointFamily.StrictCentralTorusCharacterBound i ν I χ := by
  let d := D I
  apply standardCentralExponent_norm_lt_one_of_positiveCone d.rootPresentation d.r
    d.compatible.parabolic d.compatible.levi d.radical d.multiplication I rfl (h I) (hU I)
    d.radical_points_eq d.levi_points_eq (hselected I) π ?_ χ hχ
  intro ψ hψ
  exact hcone d.P d.M d.U d.A d.p d.l d.r d.a d.compatible.parabolic
    d.compatible.levi d.radical d.multiplication d.compatible.splitComponent
    d.rootPresentation ψ hψ

/-- Conditional sufficiency, with the exact all-parabolic cone hypothesis and
arbitrary carrier universe, after the actual standard presentations, selected-root
valuation law and strict analytic sufficiency have been supplied. -/
theorem squareIntegrableModCenter_of_positiveRepresented
    (hG : IsConnectedReductive G)
    (hsq : RationalPointFamily.RationalStrictJacquetSquareIntegrabilityStatement.{u, v})
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hU : ∀ I, IsClosed (RationalPointFamily.unipotent i ν I : Set (rationalPoints G)))
    (D : ∀ I : Finset (RationalPointFamily.SimpleRoot i ν), StandardCasselmanPresentation i ν I)
    (hselected : ∀ I (t : rationalPoints T.toGrp)
      (z : Subgroup.center (RationalPointFamily.levi i ν I)),
      ((z : RationalPointFamily.levi i ν I) : rationalPoints G) = rationalPoints.map i t →
      ∀ α ∈ I, ValuativeRel.valuation k
        (RationalPointFamily.simpleRootPointValue i ν α t : k) = 1)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : π.IsAdmissible) (hc : Nonempty (UnitaryCentralCharacter π.representation))
    (hcone : HasPositiveRepresentedJacquetExponents π)
    [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
    [haar.IsHaarMeasure] :
    IsSquareIntegrableModCenter π.representation haar := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  apply RationalPointFamily.strictJacquetSquareIntegrability_arbitraryCarrier
    G hG hsq T i hi ν hν hStandard hU π hπ hc ?_ haar
  exact strictStandardExponents_of_positiveRepresented i ν D
    (RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν) hU hselected π hcone

end ConeCondition

end Langlands.Aubert.General.RepresentedParabolic
