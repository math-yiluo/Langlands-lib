import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Actual represented Levi functors under an exact dynamic presentation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private def pullbackReflIso {H : Type u} [Group H] [TopologicalSpace H] :
    SmoothRep.pullbackFunctor.{u, u, v} (ContinuousMulEquiv.refl H) ≅
      𝟭 (SmoothRep.{0, u, v} ℂ H) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun _ => rfl))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

private def pullbackTransIso
    {H K L : Type u} [Group H] [Group K] [Group L]
    [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
    (e : H ≃ₜ* K) (f : K ≃ₜ* L) :
    SmoothRep.pullbackFunctor.{u, u, v} (e.trans f) ≅
      SmoothRep.pullbackFunctor f ⋙ SmoothRep.pullbackFunctor e :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun _ => rfl))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

private def inductionIsoOfSubgroupsEq
    {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {P M U P' M' U' : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set H))
    (eP : P = P') (eM : M = M') (eU : U = U') :
    normalizedInductionFunctor.{u, v} h hU ≅
      SmoothRep.pullbackFunctor (subgroupCongrContinuous eM).symm ⋙
        normalizedInductionFunctor h' hU' := by
  subst P' M' U'
  exact (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (pullbackReflIso.symm) _

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
    {G P M U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]

local instance comparisonAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

local instance comparisonLeviTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic χ)
    (hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ)
    (hU : SubgroupFunctor.range (r ≫ p) = Dynamic.unipotent χ)

local notation "test" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- The actual Levi's canonical point group is the dynamic centralizer's
point group under the supplied exact all-test presentation. -/
def dynamicLeviPointsEquiv :
    rationalPoints M ≃ₜ* (Dynamic.centralizer χ).carrier test :=
  (leviPointsEquiv p l hp hl).trans
    (subgroupCongrContinuous (congrArg (fun F : SubgroupFunctor G => F.carrier test) hM))

omit [T2Space k] in
/-- The comparison sends each point by the original composite Levi inclusion. -/
@[simp] theorem dynamicLeviPointsEquiv_apply_coe (m : rationalPoints M) :
    (dynamicLeviPointsEquiv p l hp hl χ hM m : rationalPoints G) =
      rationalPoints.map (l ≫ p) m := rfl

include p r hp hr hU in
/-- Closedness of the dynamic radical follows from the supplied exact
presentation and the original radical's closed immersion. -/
theorem dynamicRadicalClosed :
    IsClosed ((Dynamic.unipotent χ).carrier test : Set (rationalPoints G)) := by
  have he : pointImage (r ≫ p) = (Dynamic.unipotent χ).carrier test :=
    congrArg (fun F : SubgroupFunctor G => F.carrier test) hU
  rw [← he]
  exact isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup

variable [LocallyCompactSpace (rationalPoints G)]
    [NonarchimedeanGroup (rationalPoints G)]

/-- The actual represented-Levi induction is naturally the exact dynamic
induction after the canonical coefficient pullback. -/
def leviDynamicInductionIso :
    leviInductionFunctor.{u, v} p l r hp hr hl hmul ≅
      SmoothRep.pullbackFunctor.{u, u, v}
          (dynamicLeviPointsEquiv p l hp hl χ hM).symm ⋙
        normalizedInductionFunctor.{u, v} (G := rationalPoints G)
          (dynamic_isSemidirectDecomposition χ test)
          (dynamicRadicalClosed p r hp hr χ hU) := by
  let e := leviPointsEquiv p l hp hl
  let eM := congrArg (fun F : SubgroupFunctor G => F.carrier test) hM
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hR := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let I := normalizedInductionFunctor.{u, v}
    (dynamic_isSemidirectDecomposition χ test) (dynamicRadicalClosed p r hp hr χ hU)
  have hcomp := inductionIsoOfSubgroupsEq h hR
    (dynamic_isSemidirectDecomposition χ test) (dynamicRadicalClosed p r hp hr χ hU)
    (congrArg (fun F : SubgroupFunctor G => F.carrier test) hP) eM
    (congrArg (fun F : SubgroupFunctor G => F.carrier test) hU)
  refine Functor.isoWhiskerLeft (SmoothRep.pullbackFunctor e.symm) hcomp ≪≫ ?_
  exact (Functor.associator _ _ I).symm ≪≫
    Functor.isoWhiskerRight
      (pullbackTransIso (subgroupCongrContinuous eM).symm e.symm).symm I

end Langlands.Aubert.General.RepresentedParabolic
