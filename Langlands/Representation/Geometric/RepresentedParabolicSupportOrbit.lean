import Langlands.Representation.Geometric.RepresentedParabolicSupportFiltration
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof

/-! # Actual orbit pieces of represented parabolic induction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supportOrbitAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

/-- The actual normalized inducing covariance is smooth on the parabolic image. -/
theorem isSmooth_leviInducingFunctor_obj
    (A : letI := leviPointTopology l hl
      SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    IsSmooth ((leviInducingFunctor p l r hp hr hl hmul).obj A).ρ := by
  let := leviPointTopology l hl
  let B := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm A
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  exact (isSmooth_twist_iff
    (inductionCharacter (pointImage (r ≫ p)) (pointImage p) hc h.le_normalizer).toMonoidHom
    (B.representation.comp h.projection)
    (inductionCharacter (pointImage (r ≫ p)) (pointImage p) hc h.le_normalizer).isOpen_ker).mpr
      (isSmooth_comp h.projection (continuous_projection_pointImage p l r hp hl hr hmul)
        B.isSmooth)

/-- The inducing covariance, bundled in the full smooth parabolic category. -/
def smoothLeviInducingFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
      SmoothRep.{0, u, v} ℂ (pointImage p) := by
  letI := leviPointTopology l hl
  let I := leviInducingFunctor.{u, v} p l r hp hr hl hmul
  exact {
    obj A := SmoothRep.of (I.obj A).ρ (isSmooth_leviInducingFunctor_obj p l r hp hr hl hmul A)
    map f := ObjectProperty.homMk (I.map f)
    map_id A := by
      apply ObjectProperty.hom_ext
      exact I.map_id A
    map_comp f g := by
      apply ObjectProperty.hom_ext
      exact I.map_comp f g }

@[simp]
theorem smoothLeviInducingFunctor_toRep :
    letI := leviPointTopology l hl
    smoothLeviInducingFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep =
      leviInducingFunctor p l r hp hr hl hmul := by
  rfl

variable (q : Q ⟶ G)
  [CompactSpace (Induction.LeftQuotient (pointImage p))]

/-- Compactness of the actual parabolic quotient identifies the specified
compact and smooth support quotients, keeping the same functions and indices. -/
def leviInductionSupportCompactIso {m : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) (i : Fin m) :
    letI := leviPointTopology l hl
    smoothLeviInducingFunctor.{u, v} p l r hp hr hl hmul ⋙
        (s.supportFiltration (R := ℂ)).graded i ≅
      (leviInductionSupportFiltration p l r hp hr hl hmul q s).graded i := by
  letI := leviPointTopology l hl
  exact Functor.isoWhiskerLeft (leviInducingFunctor p l r hp hr hl hmul)
    (s.rawSupportGradedCompactSmoothIso (R := ℂ) i)

variable [T2Space (rationalPoints G)] [SigmaCompactSpace (rationalPoints G)]

/-- Before target-radical coinvariants, each actual support quotient is the
compactly induced stabilizer representation of that same orbit, naturally. -/
def leviInductionSupportOrbitIso (hq : IsParabolicSubgroup q) {m : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) (i : Fin m) :
    letI := leviPointTopology l hl
    (leviInductionSupportFiltration.{u, v} p l r hp hr hl hmul q s).graded i ≅
      smoothLeviInducingFunctor p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) (s.representative i) := by
  letI := leviPointTopology l hl
  let e := Classical.choice (Geometric.closedSubgroupMackeyFiltration.{u, v} (rationalPoints G)
    (pointImage p) (pointImage q)
    (isClosed_pointImage p hp.isClosedSubgroup) (isClosed_pointImage q hq.isClosedSubgroup)
    m s i)
  exact (leviInductionSupportCompactIso p l r hp hr hl hmul q s i).symm ≪≫
    Functor.isoWhiskerLeft (smoothLeviInducingFunctor p l r hp hr hl hmul) e

end Langlands.Aubert.General.RepresentedParabolic
