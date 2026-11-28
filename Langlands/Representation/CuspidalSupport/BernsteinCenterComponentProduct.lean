import Langlands.Representation.CuspidalSupport.BernsteinComponentChange
import Langlands.Representation.CuspidalSupport.BernsteinParabolicTwistInduction

/-! # The Bernstein centre as a product of component rings -/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

open ComponentWeyl BernsteinCuspidalDatum

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] ambientAffine canonicalTopology standardLeviClosed standardLeviAffine
  BernsteinLeviPresentation.standardLeviFiniteType

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (family : BernsteinStandardFamily i ν)

/-- Choose a standard cuspidal datum in an inertial class. -/
def bernsteinComponentDatum (s : BernsteinInertialClass.{u, v} i ν family) :
    BernsteinCuspidalDatum.{u, v} i ν family :=
  Quotient.out s

/-- The chosen datum represents the specified inertial class. -/
theorem bernsteinComponentDatum_class (s : BernsteinInertialClass.{u, v} i ν family) :
    bernsteinInertialClass i ν family (bernsteinComponentDatum i ν family s) = s :=
  Quotient.out_eq s

/-- The product of the invariant regular-function rings at the chosen representatives. -/
abbrev BernsteinComponentProduct :=
  (s : BernsteinInertialClass.{u, v} i ν family) →
    (bernsteinComponentDatum i ν family s).componentAlgebra

private theorem componentDatum_related (a : BernsteinCuspidalDatum.{u, v} i ν family)
    {s : BernsteinInertialClass.{u, v} i ν family} (hs : bernsteinInertialClass i ν family a = s) :
    IsBernsteinInertiaRelated i ν family (bernsteinComponentDatum i ν family s) a :=
  (bernsteinInertialClass_eq_iff i ν family _ a).mp
    ((bernsteinComponentDatum_class i ν family s).trans hs.symm)

private def componentProductAt (f : BernsteinComponentProduct.{u, v} i ν family)
    (a : BernsteinCuspidalDatum.{u, v} i ν family)
    {s : BernsteinInertialClass.{u, v} i ν family} (hs : bernsteinInertialClass i ν family a = s) :
    a.componentAlgebra :=
  componentEquiv (componentDatum_related i ν family a hs) (f s)

/-- Express the coordinate of a function in the component ring of an arbitrary datum. -/
def componentProductOn (f : BernsteinComponentProduct.{u, v} i ν family)
    (a : BernsteinCuspidalDatum.{u, v} i ν family) : a.componentAlgebra :=
  componentProductAt i ν family f a rfl

private theorem componentProductAt_eq (f : BernsteinComponentProduct.{u, v} i ν family)
    (a : BernsteinCuspidalDatum.{u, v} i ν family)
    {s : BernsteinInertialClass.{u, v} i ν family} (hs : bernsteinInertialClass i ν family a = s) :
    componentProductAt i ν family f a hs = componentProductOn i ν family f a := by
  subst s
  rfl

/-- The product coordinate has the same value at any associated parameter. -/
theorem componentProductOn_eval (f : BernsteinComponentProduct.{u, v} i ν family)
    (s : BernsteinInertialClass.{u, v} i ν family) (a : BernsteinCuspidalDatum.{u, v} i ν family)
    {χ : (bernsteinComponentDatum i ν family s).unramifiedParameter} {ψ : a.unramifiedParameter}
    (h : (bernsteinComponentDatum i ν family s).TwistsAssociated a χ ψ) :
    a.componentEval ψ (componentProductOn i ν family f a) =
      (bernsteinComponentDatum i ν family s).componentEval χ (f s) := by
  have hs := h.inertialClass_eq.symm.trans (bernsteinComponentDatum_class i ν family s)
  rw [← componentProductAt_eq i ν family f a hs]
  exact componentEquiv_eval _ _ h

private theorem componentProductOn_compatible (f : BernsteinComponentProduct.{u, v} i ν family)
    (a b : BernsteinCuspidalDatum.{u, v} i ν family)
    {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter} (h : a.TwistsAssociated b χ ψ) :
    a.componentEval χ (componentProductOn i ν family f a) =
      b.componentEval ψ (componentProductOn i ν family f b) := by
  let s := bernsteinInertialClass i ν family a
  have hs := componentDatum_related i ν family a (s := s) rfl
  obtain ⟨ω, hω⟩ := exists_associated_parameter hs χ
  exact (componentProductOn_eval i ν family f s a hω).trans
    (componentProductOn_eval i ν family f s b (hω.trans h)).symm

private theorem componentProductOn_datum (f : BernsteinComponentProduct.{u, v} i ν family)
    (s : BernsteinInertialClass.{u, v} i ν family) :
    componentProductOn i ν family f (bernsteinComponentDatum i ν family s) = f s := by
  apply componentAlgebra_ext
  intro χ
  exact componentProductOn_eval i ν family f s _ (TwistsAssociated.refl _ χ)

section Centre

variable (hS : BernsteinCenterFunctionsStatement.{u, v})

include hS in
private theorem exists_centerFunctions
    (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G))) :
    ∃ g : (a : BernsteinCuspidalDatum.{u, max u v} i ν family) → a.componentAlgebra,
      (∀ (a b : BernsteinCuspidalDatum.{u, max u v} i ν family)
          (χ : a.unramifiedParameter) (ψ : b.unramifiedParameter),
        a.TwistsAssociated b χ ψ → a.componentEval χ (g a) = b.componentEval ψ (g b)) ∧
      ∀ (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter),
        ActsByScalar z (a.twistInduction χ) (a.componentEval χ (g a)) := by
  have h := hS F G T i ν family
  obtain ⟨f, hf, hscalar⟩ := h.1 z
  let g (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter) : ℂ :=
    f a χ.val.toMonoidHom
  let reg (a : BernsteinCuspidalDatum.{u, max u v} i ν family) :
      unramifiedRegularFunctions
        (fun q => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) q).toMul) :=
    ⟨g a, (hf a).1⟩
  let entry (a : BernsteinCuspidalDatum.{u, max u v} i ν family) : a.componentAlgebra :=
    ⟨reg a, (mem_invariantAlgebra_iff _ _ (reg a)).mpr (fun χ ψ hχ => (hf a).2 a χ ψ hχ)⟩
  refine ⟨entry, ?_, ?_⟩
  · intro a b χ ψ hχ
    change g a χ = g b ψ
    exact (hf a).2 b χ ψ hχ
  · intro a χ x
    change _ = g a χ • x
    with_reducible exact hscalar a χ x

private def centerFunctions (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) : a.componentAlgebra :=
  (exists_centerFunctions i ν family hS z).choose a

private theorem centerFunctions_compatible
    (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a b : BernsteinCuspidalDatum.{u, max u v} i ν family)
    {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter} (hχ : a.TwistsAssociated b χ ψ) :
    a.componentEval χ (centerFunctions i ν family hS z a) =
      b.componentEval ψ (centerFunctions i ν family hS z b) :=
  (exists_centerFunctions i ν family hS z).choose_spec.1 a b χ ψ hχ

private theorem centerFunctions_scalar (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter) :
    ActsByScalar z (a.twistInduction χ) (a.componentEval χ (centerFunctions i ν family hS z a)) :=
  (exists_centerFunctions i ν family hS z).choose_spec.2 a χ

private theorem centerFunctions_unique (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter) {c : ℂ}
    (hc : ActsByScalar z (a.twistInduction χ) c) :
    a.componentEval χ (centerFunctions i ν family hS z a) = c := by
  let : Nontrivial (a.twistInduction χ) := by
    with_reducible exact nontrivial_twistInduction.{u, v} i ν family a χ
  exact SmoothRep.scalar_unique (z.app (a.twistInduction χ))
    (centerFunctions_scalar i ν family hS z a χ) hc

private theorem centerFunctions_add (z w : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) :
    centerFunctions i ν family hS (z + w) a =
      centerFunctions i ν family hS z a + centerFunctions i ν family hS w a := by
  apply componentAlgebra_ext
  intro χ
  refine centerFunctions_unique i ν family hS (z + w) a χ
    (c := a.componentEval χ (centerFunctions i ν family hS z a) +
      a.componentEval χ (centerFunctions i ν family hS w a)) ?_
  intro x
  rw [CatCenter.app_add]
  change SmoothRep.hom (z.app (a.twistInduction χ)) x +
    SmoothRep.hom (w.app (a.twistInduction χ)) x = (_ + _) • x
  rw [centerFunctions_scalar i ν family hS z a χ x,
    centerFunctions_scalar i ν family hS w a χ x, add_smul]

private theorem actsByScalar_mul {Q : Type u} [Group Q] [TopologicalSpace Q]
    (V : SmoothRep.{0, u, v} ℂ Q) (z w : CatCenter (SmoothRep.{0, u, v} ℂ Q)) {c d : ℂ}
    (hz : ActsByScalar z V c) (hw : ActsByScalar w V d) : ActsByScalar (z * w) V (c * d) := by
  intro x
  rw [CatCenter.mul_app']
  change SmoothRep.hom (z.app V) (SmoothRep.hom (w.app V) x) = (c * d) • x
  rw [hw x, map_smul, hz x, smul_smul, mul_comm d c]

private theorem centerFunctions_mul (z w : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) :
    centerFunctions i ν family hS (z * w) a =
      centerFunctions i ν family hS z a * centerFunctions i ν family hS w a := by
  apply componentAlgebra_ext
  intro χ
  refine centerFunctions_unique i ν family hS (z * w) a χ
    (c := a.componentEval χ (centerFunctions i ν family hS z a) *
      a.componentEval χ (centerFunctions i ν family hS w a)) ?_
  exact actsByScalar_mul (a.twistInduction χ) z w
    (centerFunctions_scalar i ν family hS z a χ) (centerFunctions_scalar i ν family hS w a χ)

private def centerCoordinates : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) →+*
    BernsteinComponentProduct.{u, max u v} i ν family where
  toFun z s := centerFunctions i ν family hS z (bernsteinComponentDatum i ν family s)
  map_zero' := by
    funext s
    apply componentAlgebra_ext
    intro χ
    exact centerFunctions_unique i ν family hS 0 _ χ (fun x => (zero_smul ℂ x).symm)
  map_one' := by
    funext s
    apply componentAlgebra_ext
    intro χ
    exact centerFunctions_unique i ν family hS 1 _ χ (fun x => (one_smul ℂ x).symm)
  map_add' z w := funext (fun s => centerFunctions_add i ν family hS z w
    (bernsteinComponentDatum i ν family s))
  map_mul' z w := funext (fun s => centerFunctions_mul i ν family hS z w
    (bernsteinComponentDatum i ν family s))

private theorem centerCoordinates_scalar
    (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter) :
    ActsByScalar z (a.twistInduction χ)
      (a.componentEval χ (componentProductOn i ν family (centerCoordinates i ν family hS z) a)) := by
  let s := bernsteinInertialClass i ν family a
  have hs := componentDatum_related i ν family a (s := s) rfl
  obtain ⟨ω, hω⟩ := exists_associated_parameter hs χ
  rw [componentProductOn_eval i ν family _ s a hω]
  change ActsByScalar z (a.twistInduction χ) ((bernsteinComponentDatum i ν family s).componentEval ω
    (centerFunctions i ν family hS z (bernsteinComponentDatum i ν family s)))
  rw [centerFunctions_compatible i ν family hS z _ a hω]
  exact centerFunctions_scalar i ν family hS z a χ

private theorem centerCoordinates_injective : Function.Injective (centerCoordinates i ν family hS) := by
  intro z w hzw
  have h := hS F G T i ν family
  apply h.2.1 z w
  intro a Xa twista inda χ
  have hz := centerCoordinates_scalar i ν family hS z a χ
  have hw := centerCoordinates_scalar i ν family hS w a χ
  rw [hzw] at hz
  apply ObjectProperty.hom_ext
  ext x
  exact (hz x).trans (hw x).symm

include hS in
private theorem exists_center_of_componentProduct
    (f : BernsteinComponentProduct.{u, max u v} i ν family) :
    ∃ z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      ∀ (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter),
        ActsByScalar z (a.twistInduction χ) (a.componentEval χ (componentProductOn i ν family f a)) := by
  let g (a : BernsteinCuspidalDatum.{u, max u v} i ν family) : a.unramifiedParameter → ℂ := fun χ =>
    a.componentEval χ (componentProductOn i ν family f a)
  let fext (a : BernsteinCuspidalDatum.{u, max u v} i ν family) := extendUnramified i ν family a (g a)
  have h := hS F G T i ν family
  have hz := h.2.2 fext (by
    intro a Xa twista inda
    refine ⟨?_, ?_⟩
    · have heval : (fun ω : Xa => fext a ω.val.toMonoidHom) = g a :=
        funext (extendUnramified_apply i ν family a (g a))
      rw [heval]
      exact (componentProductOn i ν family f a).val.property
    · intro b Xb twistb indb ω ω' hω
      change extendUnramified i ν family a (g a) ω.val.toMonoidHom =
        extendUnramified i ν family b (g b) ω'.val.toMonoidHom
      rw [extendUnramified_apply, extendUnramified_apply]
      exact componentProductOn_compatible i ν family f a b hω)
  obtain ⟨z, hscalar⟩ := hz
  refine ⟨z, fun a χ x => ?_⟩
  exact (hscalar a χ x).trans (congrArg (· • x)
    (extendUnramified_apply i ν family a (g a) χ))

private theorem centerCoordinates_surjective : Function.Surjective (centerCoordinates i ν family hS) := by
  intro f
  obtain ⟨z, hscalar⟩ := exists_center_of_componentProduct i ν family hS f
  refine ⟨z, funext fun s => ?_⟩
  apply componentAlgebra_ext
  intro χ
  let a := bernsteinComponentDatum i ν family s
  have hc := hscalar a χ
  rw [componentProductOn_datum i ν family f s] at hc
  change a.componentEval χ (centerFunctions i ν family hS z a) = a.componentEval χ (f s)
  exact centerFunctions_unique i ν family hS z a χ hc

/-- The global Bernstein centre is isomorphic to the product of its component rings. -/
def centerComponentProductEquiv : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) ≃+*
    BernsteinComponentProduct.{u, max u v} i ν family :=
  RingEquiv.ofBijective (centerCoordinates i ν family hS)
    ⟨centerCoordinates_injective i ν family hS, centerCoordinates_surjective i ν family hS⟩

/-- The product coordinates give the central scalar on every twisted induction. -/
theorem centerComponentProductEquiv_scalar
    (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter) :
    ActsByScalar z (a.twistInduction χ)
      (a.componentEval χ
        (componentProductOn i ν family (centerComponentProductEquiv i ν family hS z) a)) :=
  centerCoordinates_scalar i ν family hS z a χ

/-- The product description of the centre and its evaluation law, from the scalar description. -/
def BernsteinCenterComponentProductStatement : Prop :=
  BernsteinCenterFunctionsStatement.{u, v} →
    ∃ e : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) ≃+*
        BernsteinComponentProduct.{u, max u v} i ν family,
      ∀ (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
        (a : BernsteinCuspidalDatum.{u, max u v} i ν family) (χ : a.unramifiedParameter),
        ActsByScalar z (a.twistInduction χ)
          (a.componentEval χ (componentProductOn i ν family (e z) a))

/-- The product equivalence satisfies the scalar description on every datum. -/
theorem bernsteinCenterComponentProduct :
    BernsteinCenterComponentProductStatement.{u, v} i ν family := by
  intro hS
  refine ⟨centerComponentProductEquiv.{u, v} i ν family hS, ?_⟩
  intro z a χ
  exact centerComponentProductEquiv_scalar.{u, v} i ν family hS z a χ

end Centre

end Langlands.CuspidalSupport
