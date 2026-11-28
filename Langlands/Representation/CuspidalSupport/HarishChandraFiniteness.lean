import Langlands.Representation.CuspidalSupport.HarishChandraHomomorphismReduction
import Langlands.Representation.CuspidalSupport.BernsteinLeviComponentProduct

/-! # Harish-Chandra finiteness from the description of the Bernstein centre -/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.CuspidalSupport Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj IsMulCommutative

namespace Langlands.Aubert.General.RepresentedParabolic

open BernsteinCuspidalDatum

universe u v

attribute [local instance] ambientAffine canonicalTopology standardLeviClosed standardLeviAffine
  BernsteinLeviPresentation.standardLeviFiniteType

private theorem moduleFinite_of_commuting_ringEquivs
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (eG : R ≃+* R') (eM : S ≃+* S')
    (h : ∀ z, eM (φ z) = ψ (eG z)) (hψ : ψ.Finite) :
    letI : Module R S := Module.compHom _ φ
    Module.Finite R S := by
  have hφ : φ = eM.symm.toRingHom.comp (ψ.comp eG.toRingHom) := by
    ext z
    exact (eM.symm_apply_apply (φ z)).symm.trans (congrArg eM.symm (h z))
  change φ.Finite
  rw [hφ]
  exact eM.symm.finite.comp (hψ.comp eG.finite)

/-- The finiteness in Renard VI.10.5 follows from the description of global central scalars. -/
def HarishChandraFinitenessFromCenterFunctionsStatement : Prop :=
  BernsteinCenterFunctionsStatement.{u, v} → HarishChandraFinitenessStatement.{u, v}

set_option allowUnsafeReducibility true in
attribute [local reducible] BernsteinLeviPresentation.ambientDatum in
/-- Induction compatibility identifies a centre map with finite restriction on component
rings, using the scalar description of the Bernstein centre. -/
theorem harishChandraFiniteness_of_centerFunctions :
    HarishChandraFinitenessFromCenterFunctionsStatement.{u, v} := by
  intro hS k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro I φ hφ
  have := hG.smooth
  have := hl.isConnectedReductive.smooth
  let A := (exists_bernsteinParabolicPresentation hG p l r hp hl hr).some
  let D := A.leviPresentation hp hl
  let eG := centerComponentProductEquiv.{u, v} A.inclusion A.cocharacter A.family hS
  let eM := centerComponentProductEquiv.{u, v} D.torus A.cocharacter (D.standardFamily A.family) hS
  let ψ := D.componentProductHom.{u, max u v} A.family
  refine @moduleFinite_of_commuting_ringEquivs
    (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)))
    (BernsteinComponentProduct.{u, max u v} A.inclusion A.cocharacter A.family)
    (BernsteinComponentProduct.{u, max u v} D.torus A.cocharacter (D.standardFamily A.family))
    inferInstance inferInstance inferInstance inferInstance
    φ ψ eG eM ?_ (D.componentProductHom_finite.{u, max u v} A.family)
  intro z
  funext s
  apply componentAlgebra_ext
  intro χ
  let a := bernsteinComponentDatum D.torus A.cocharacter (D.standardFamily A.family) s
  let b := (D.ambientDatum A.family a).val
  let ω : b.unramifiedParameter := by
    with_reducible exact rationalUnramifiedCharacterTransport (D.innerLeviIso A.family a.roots) χ
  have hc := centerComponentProductEquiv_scalar.{u, v} D.torus A.cocharacter
    (D.standardFamily A.family) hS (φ z) a χ
  have hd := centerComponentProductEquiv_scalar.{u, v} A.inclusion A.cocharacter
    A.family hS z b ω
  have hscalar := A.twistInduction_scalar_eq.{u, v} hp hl hr hmul
  unfold BernsteinParabolicPresentation.TwistInductionScalarsAgree at hscalar
  have heq :
      a.componentEval χ (componentProductOn D.torus A.cocharacter (D.standardFamily A.family)
        (eM (φ z)) a) =
        b.componentEval ω (componentProductOn A.inclusion A.cocharacter A.family (eG z) b) := by
    with_reducible exact hscalar a χ z (φ z) (hφ z) hc hd
  have hEvalM := componentProductOn_eval D.torus A.cocharacter (D.standardFamily A.family)
    (eM (φ z)) s a (TwistsAssociated.refl a χ)
  have hEvalG := D.componentProductHom_eval.{u, max u v} A.family (eG z) s χ
  exact hEvalM.symm.trans (heq.trans hEvalG.symm)

end Langlands.Aubert.General.RepresentedParabolic
