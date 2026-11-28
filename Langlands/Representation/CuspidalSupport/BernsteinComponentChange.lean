import Langlands.Representation.CuspidalSupport.BernsteinComponentVarietyProof
import Langlands.Representation.CuspidalSupport.BernsteinInnerComponent
import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsReduction

/-! # Change of cuspidal datum for a Bernstein component -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport.BernsteinCuspidalDatum

open ComponentWeyl

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] ambientAffine canonicalTopology standardLeviClosed standardLeviAffine
  BernsteinLeviPresentation.standardLeviFiniteType

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {family : BernsteinStandardFamily i ν}

/-- Unramified characters of the inducing Levi of a cuspidal datum. -/
abbrev unramifiedParameter (a : BernsteinCuspidalDatum.{u, v} i ν family) :=
  UChar (bernsteinLeviScheme i ν a.roots)

/-- The invariant algebra on the parameter torus of the datum. -/
abbrev componentAlgebra (a : BernsteinCuspidalDatum.{u, v} i ν family) :=
  invariantAlgebra (Standard.leviHom i ν (rootSet i ν a.roots)) a.representation

/-- Association of the twists specified by two unramified parameters. -/
abbrev TwistsAssociated (a b : BernsteinCuspidalDatum.{u, v} i ν family)
    (χ : a.unramifiedParameter) (ψ : b.unramifiedParameter) : Prop :=
  ComponentWeyl.TwistsAssociated (Standard.leviHom i ν (rootSet i ν a.roots))
    (Standard.leviHom i ν (rootSet i ν b.roots)) a.representation b.representation χ ψ

variable {a b d : BernsteinCuspidalDatum.{u, v} i ν family}

/-- Evaluation of an invariant function at an unramified character. -/
def componentEval (a : BernsteinCuspidalDatum.{u, v} i ν family)
    (χ : a.unramifiedParameter) : a.componentAlgebra →+* ℂ where
  toFun f := f.val.val χ
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Evaluations determine an invariant regular function. -/
theorem componentAlgebra_ext {f g : a.componentAlgebra}
    (h : ∀ χ, a.componentEval χ f = a.componentEval χ g) : f = g :=
  Subtype.ext (Subtype.ext (funext h))

/-- Invariant functions take equal values at associated parameters of the same datum. -/
theorem componentEval_eq (f : a.componentAlgebra) {χ ψ : a.unramifiedParameter}
    (h : a.TwistsAssociated a χ ψ) : a.componentEval χ f = a.componentEval ψ f :=
  (mem_invariantAlgebra_iff _ _ f.val).mp f.property χ ψ h

/-- A parameter is associated to itself. -/
theorem TwistsAssociated.refl (a : BernsteinCuspidalDatum.{u, v} i ν family)
    (χ : a.unramifiedParameter) : a.TwistsAssociated a χ χ :=
  ⟨RationalLeviConjugacy.refl _, ⟨(rationalIsoPullbackReflIso (rationalUnramifiedTwist _ χ
    a.representation)).symm⟩⟩

/-- Association of twisted data is symmetric. -/
theorem TwistsAssociated.symm {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter}
    (h : a.TwistsAssociated b χ ψ) : b.TwistsAssociated a ψ χ := by
  obtain ⟨c, ⟨e⟩⟩ := h
  let cancel := rationalIsoPullbackCancelIso c.iso.symm (rationalUnramifiedTwist _ ψ b.representation)
  rw [Iso.symm_symm_eq] at cancel
  exact ⟨c.symm, ⟨cancel.symm ≪≫ (pullback_congr c.iso.symm ⟨e.symm⟩).some⟩⟩

/-- Association of twisted data is transitive. -/
theorem TwistsAssociated.trans {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter}
    {ω : d.unramifiedParameter} (h : a.TwistsAssociated b χ ψ) (k : b.TwistsAssociated d ψ ω) :
    a.TwistsAssociated d χ ω := by
  obtain ⟨c, ⟨e⟩⟩ := h
  obtain ⟨c', ⟨e'⟩⟩ := k
  exact ⟨c.trans c', ⟨e ≪≫ (pullback_congr c.iso ⟨e'⟩).some ≪≫
    rationalIsoPullbackTransIso c.iso c'.iso (rationalUnramifiedTwist _ ω d.representation)⟩⟩

/-- Associated twists belong to one inertial class. -/
theorem TwistsAssociated.inertialClass_eq {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter}
    (h : a.TwistsAssociated b χ ψ) :
    bernsteinInertialClass i ν family a = bernsteinInertialClass i ν family b := by
  apply (bernsteinInertialClass_eq_iff i ν family a b).mpr
  exact (component_transfer (Standard.leviHom i ν (rootSet i ν a.roots)) a.representation
    (Standard.leviHom i ν (rootSet i ν b.roots)) b.representation).1.mp ⟨χ, ψ, h⟩

/-- Every parameter of an inertially equivalent datum is reached by an associated twist. -/
theorem exists_associated_parameter (h : IsBernsteinInertiaRelated i ν family a b)
    (ψ : b.unramifiedParameter) : ∃ χ, a.TwistsAssociated b χ ψ :=
  exists_twist_association i ν family a b h ψ

private theorem exists_componentTransport (h : IsBernsteinInertiaRelated i ν family a b)
    (f : a.componentAlgebra) : ∃ g : b.componentAlgebra, ∀ χ ψ,
      a.TwistsAssociated b χ ψ → b.componentEval ψ g = a.componentEval χ f := by
  have htransfer := (component_transfer (Standard.leviHom i ν (rootSet i ν a.roots)) a.representation
    (Standard.leviHom i ν (rootSet i ν b.roots)) b.representation).2 h
  obtain ⟨g, hg, heval⟩ := htransfer.2 f.val.val
    ⟨f.val.property, fun χ ψ hχψ => componentEval_eq f hχψ⟩
  refine ⟨⟨⟨g, hg⟩, (mem_invariantAlgebra_iff _ _ ⟨g, hg⟩).mpr ?_⟩, heval⟩
  intro ψ ω hψω
  obtain ⟨χ, hχ⟩ := exists_associated_parameter h ψ
  exact (heval χ ψ hχ).trans (heval χ ω (hχ.trans hψω)).symm

private def componentTransport (h : IsBernsteinInertiaRelated i ν family a b)
    (f : a.componentAlgebra) : b.componentAlgebra :=
  (exists_componentTransport h f).choose

private theorem componentTransport_eval (h : IsBernsteinInertiaRelated i ν family a b)
    (f : a.componentAlgebra) {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter}
    (hχ : a.TwistsAssociated b χ ψ) :
    b.componentEval ψ (componentTransport h f) = a.componentEval χ f :=
  (exists_componentTransport h f).choose_spec χ ψ hχ

private theorem componentTransport_leftInverse (h : IsBernsteinInertiaRelated i ν family a b) :
    Function.LeftInverse (componentTransport h.symm) (componentTransport h) := by
  intro f
  apply componentAlgebra_ext
  intro χ
  obtain ⟨ψ, hψ⟩ := exists_associated_parameter h.symm χ
  rw [componentTransport_eval h.symm _ hψ, componentTransport_eval h _ hψ.symm]

private theorem componentTransport_mul (h : IsBernsteinInertiaRelated i ν family a b)
    (f g : a.componentAlgebra) :
    componentTransport h (f * g) = componentTransport h f * componentTransport h g := by
  apply componentAlgebra_ext
  intro ψ
  obtain ⟨χ, hχ⟩ := exists_associated_parameter h ψ
  change b.componentEval ψ (componentTransport h (f * g)) =
    b.componentEval ψ (componentTransport h f) * b.componentEval ψ (componentTransport h g)
  exact (componentTransport_eval h (f * g) hχ).trans
    (congrArg₂ (· * ·) (componentTransport_eval h f hχ) (componentTransport_eval h g hχ)).symm

private theorem componentTransport_add (h : IsBernsteinInertiaRelated i ν family a b)
    (f g : a.componentAlgebra) :
    componentTransport h (f + g) = componentTransport h f + componentTransport h g := by
  apply componentAlgebra_ext
  intro ψ
  obtain ⟨χ, hχ⟩ := exists_associated_parameter h ψ
  change b.componentEval ψ (componentTransport h (f + g)) =
    b.componentEval ψ (componentTransport h f) + b.componentEval ψ (componentTransport h g)
  exact (componentTransport_eval h (f + g) hχ).trans
    (congrArg₂ (· + ·) (componentTransport_eval h f hχ) (componentTransport_eval h g hχ)).symm

/-- Inertially equivalent data give isomorphic algebras of invariant regular functions. -/
def componentEquiv (h : IsBernsteinInertiaRelated i ν family a b) :
    a.componentAlgebra ≃+* b.componentAlgebra where
  toFun := componentTransport h
  invFun := componentTransport h.symm
  left_inv := componentTransport_leftInverse h
  right_inv := componentTransport_leftInverse h.symm
  map_mul' := componentTransport_mul h
  map_add' := componentTransport_add h

/-- The change of datum preserves values at associated parameters. -/
theorem componentEquiv_eval (h : IsBernsteinInertiaRelated i ν family a b)
    (f : a.componentAlgebra) {χ : a.unramifiedParameter} {ψ : b.unramifiedParameter}
    (hχ : a.TwistsAssociated b χ ψ) :
    b.componentEval ψ (componentEquiv h f) = a.componentEval χ f :=
  componentTransport_eval h f hχ

/-- A change of cuspidal datum within an inertial component preserves the coordinate algebra
and its evaluations at associated twists. -/
def ComponentChangeStatement (a b : BernsteinCuspidalDatum.{u, v} i ν family) : Prop :=
  IsBernsteinInertiaRelated i ν family a b →
    ∃ e : a.componentAlgebra ≃+* b.componentAlgebra,
      ∀ f χ ψ, a.TwistsAssociated b χ ψ → b.componentEval ψ (e f) = a.componentEval χ f

/-- The component equivalence gives the change of datum. -/
theorem componentChange (a b : BernsteinCuspidalDatum.{u, v} i ν family) :
    a.ComponentChangeStatement b :=
  fun h => ⟨componentEquiv h, fun f _ _ hχ => componentEquiv_eval h f hχ⟩

end Langlands.CuspidalSupport.BernsteinCuspidalDatum
