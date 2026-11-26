import Langlands.Representation.CuspidalSupport.HarishChandraHomomorphismStatement
import Langlands.Representation.CuspidalSupport.LeviCenterComponentsLift

/-! # Harish-Chandra homomorphisms from lifted central components and finiteness (Renard VI.10.5)

`HarishChandraHomomorphismStatement` follows from the existence of lifts of central components
through `i_P^G` (`LeviCenterComponentsLiftStatement`) together with the finiteness of the centre
of `M(M)` over that of `M(G)` through any ring homomorphism compatible with induction
(`HarishChandraFinitenessStatement`). With the published reduction of the lifts, it follows from
second adjointness, the joint special-compact basis and that finiteness.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.5, finiteness, in derived form: for an actual rational parabolic `P = MN` of a
connected reductive `G` and every ring homomorphism `φ : ℨ(G) → ℨ(M)` between the centres of
the categories of smooth representations (carriers in the common universe `max u v`) such that
`i_P^G((φ z)_σ) = z_{i_P^G σ}` for all `z` and `σ`, the centre `ℨ(M)` is a finitely generated
`ℨ(G)`-module through `φ`. -/
def HarishChandraFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      let I := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
      ∀ φ : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) →+*
          CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
        (∀ (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
            (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
          I.map ((φ z).app σ) = z.app (I.obj σ)) →
        letI : Module (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
            (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M))) :=
          Module.compHom _ φ
        Module.Finite (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
          (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)))

/-- The Harish-Chandra homomorphism from lifts of central components and finiteness. -/
theorem harishChandraHomomorphism_of_lift_of_finite
    (hlift : LeviCenterComponentsLiftStatement.{u, v})
    (hfin : HarishChandraFinitenessStatement.{u, v}) :
    HarishChandraHomomorphismStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have h : Renard.CenterComponentsLift (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul) :=
    hlift k G hG P M N p l r hp hl hr hmul
  have hind := leviCenterDescent_induction p l r hp hr hl hmul h
  exact ⟨leviCenterDescent p l r hp hr hl hmul h, hind,
    leviCenterDescent_jacquet p l r hp hr hl hmul h,
    hfin k G hG P M N p l r hp hl hr hmul _ hind⟩

/-- The statement that the Harish-Chandra homomorphism (Renard VI.10.5) follows from the second
adjointness theorem (Renard VI.9.6), the joint special-compact basis (Renard V.5.1–V.5.2) and
the finiteness statement `HarishChandraFinitenessStatement`. -/
def HarishChandraHomomorphismReductionStatement : Prop :=
  LeviSecondAdjointnessStatement.{u, v} →
    JointSpecialCompactBasisExistenceStatement.{u} →
      HarishChandraFinitenessStatement.{u, v} →
        HarishChandraHomomorphismStatement.{u, v}

/-- **Renard VI.10.5 from second adjointness, the joint special-compact basis and
finiteness.** -/
theorem harishChandraHomomorphismReductionStatement_holds :
    HarishChandraHomomorphismReductionStatement.{u, v} := fun hSA hJ hfin =>
  harishChandraHomomorphism_of_lift_of_finite
    (leviCenterComponentsLiftReductionStatement_holds hSA hJ) hfin

end Langlands.Aubert.General.RepresentedParabolic
