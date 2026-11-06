import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.GroupScheme.Rational.LeviRetraction

/-! # Continuous represented Levi projection and induction admissibility

The projection of the literal point-image semidirect decomposition agrees with
the point map of the algebraic Levi retraction. It is therefore continuous.
Compactness of the actual parabolic quotient then gives admissibility of
normalized induction on representations of the Levi's own rational points.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inductionAdmissibilityPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- The actual semidirect Levi projection on literal rational-point images is
continuous for the canonical ambient point topology and its subgroup topologies. -/
theorem continuous_projection_pointImage (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    Continuous
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : IsAffine P.X.left := isAffine_of_isAffineHom p.hom.hom.left
  have : IsClosedImmersion (l ≫ p).hom.hom.left :=
    hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsAffine M.X.left := isAffine_of_isAffineHom (l ≫ p).hom.hom.left
  let : TopologicalSpace (rationalPoints P) := rationalPointTopology k P.X
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let eP : rationalPoints P ≃ₜ* pointImage p :=
    (rationalPointSubgroupHomeomorph k (SubgroupFunctor.range p) p
      hp.isClosedSubgroup.isRepresentedBy_range hp.isClosedSubgroup).trans
        (subgroupCongrContinuous (pointImage_eq_range_carrier p).symm)
  let eM := leviPointsEquiv p l hp hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let : IsIso (subgroupMultiplication l r) := hmul
  let q := leviRetraction l r hr.1.isNormal
  have hq : Continuous (rationalPoints.map q) :=
    continuous_rationalPointMap k q.hom.hom
  have hcomp (x : rationalPoints P) :
      h.projection (eP x) = eM (rationalPoints.map q x) := by
    obtain ⟨a, n, han⟩ := exists_pointMultiplication l r hmul x
    have hqx : rationalPoints.map q x = a := by
      change x ≫ q.hom.hom = a
      rw [comp_leviRetraction]
      rw [← han]
      exact leviComponent_product l r a n
    have hx : eP x =
        (⟨rationalPoints.map (l ≫ p) a, pointImage_comp_le p l ⟨a, rfl⟩⟩ :
          pointImage p) *
        ⟨rationalPoints.map (r ≫ p) n, pointImage_comp_le p r ⟨n, rfl⟩⟩ := by
      apply Subtype.ext
      change rationalPoints.map p x =
        rationalPoints.map (l ≫ p) a * rationalPoints.map (r ≫ p) n
      rw [pointMap_comp_apply, pointMap_comp_apply, ← map_mul, han]
    rw [hx, hqx]
    exact h.projection_mul (eM a) ⟨rationalPoints.map (r ≫ p) n, ⟨n, rfl⟩⟩
  have heq : (fun x => h.projection x) =
      eM ∘ rationalPoints.map q ∘ eP.symm := by
    funext x
    simpa only [eP.apply_symm_apply, Function.comp_apply] using hcomp (eP.symm x)
  change Continuous (fun x => h.projection x)
  rw [heq]
  exact eM.continuous.comp (hq.comp eP.symm.continuous)

/-- The continuous Levi projection of the represented parabolic, with the same
underlying homomorphism used by the published normalized induction functor. -/
def pointImageLeviProjection (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    pointImage p →ₜ* pointImage (l ≫ p) where
  toMonoidHom :=
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection
  continuous_toFun := continuous_projection_pointImage p l r hp hl hr hmul

@[simp] theorem pointImageLeviProjection_toMonoidHom (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    (pointImageLeviProjection p l r hp hl hr hmul).toMonoidHom =
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection :=
  rfl

section Admissibility

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- With compact actual parabolic quotient, normalized induction of an admissible
representation of the Levi image is admissible. -/
theorem inductionFunctor_obj_isAdmissible (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (σ : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p))) (hσ : σ.IsAdmissible) :
    ((inductionFunctor p l r hp hr hl hmul).obj σ).IsAdmissible :=
  normalizedInductionFunctor_obj_isAdmissible
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul) σ hσ

/-- With compact actual parabolic quotient, the published transported normalized
induction takes admissible representations of `M(k)` to admissible representations. -/
theorem leviInductionFunctor_obj_isAdmissible (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (σ : let := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : let := leviPointTopology l hl; σ.IsAdmissible) :
    let := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsAdmissible := by
  let := leviPointTopology l hl
  exact inductionFunctor_obj_isAdmissible p l r hp hl hr hmul
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)
    (isAdmissible_comp_continuousMulEquiv σ.representation (leviPointsEquiv p l hp hl).symm hσ)

/-- The represented quotient-compactness statement supplies the only extra input
to the preceding induction-admissibility theorem. -/
theorem leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    (hcompact : ArbitraryParabolicQuotientCompactStatement.{u}) (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : let := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : let := leviPointTopology l hl; σ.IsAdmissible) :
    let := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsAdmissible := by
  let := hcompact k G hG P p hp
  exact leviInductionFunctor_obj_isAdmissible p l r hp hl hr hmul σ hσ

end Admissibility

end Langlands.Aubert.General.RepresentedParabolic
