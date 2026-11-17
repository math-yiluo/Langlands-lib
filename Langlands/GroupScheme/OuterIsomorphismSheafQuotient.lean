import Langlands.GroupScheme.OuterIsomorphismScheme
import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientOrbitRelation

/-! # Exact outer orbits from represented fppf action quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SchemeAction

variable {S : Scheme.{u}} {A : GroupScheme S} {X : Over S}
  (b : SchemeAction A X)

/-- Freeness on all tests glues an fppf-local acting point to a unique point
on the original test. -/
theorem existsUnique_act_of_orbitSieve_mem
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    {T : Over S} (p q : T ⟶ X)
    (hR : ActionQuotientOrbitRelation.orbitSieve b q p ∈ fppfTopology S T) :
    ∃! d : T ⟶ A.X, b.act d p = q := by
  let R := ActionQuotientOrbitRelation.orbitSieve b q p
  let x : Presieve.FamilyOfElements ((schemeYoneda S).obj A.X) R.arrows :=
    fun _ f hf => ⟨hf.choose⟩
  have hx : x.Compatible := by
    intro V W Z r s f g hf hg hrs
    apply ULift.ext
    apply hfree Z ((r ≫ f) ≫ p)
    have h₁ : b.act (r ≫ hf.choose) ((r ≫ f) ≫ p) = (r ≫ f) ≫ q := by
      rw [Category.assoc, ← b.naturality, ← hf.choose_spec, Category.assoc]
    have h₂ : b.act (s ≫ hg.choose) ((s ≫ g) ≫ p) = (s ≫ g) ≫ q := by
      rw [Category.assoc, ← b.naturality, ← hg.choose_spec, Category.assoc]
    change b.act (r ≫ hf.choose) ((r ≫ f) ≫ p) =
      b.act (s ≫ hg.choose) ((r ≫ f) ≫ p)
    rw [h₁, hrs, h₂]
  have hA := (isSheaf_iff_isSheaf_of_type _ _).mp ((schemeSheaf S).obj A.X).property
  obtain ⟨d, hd, -⟩ := hA R hR x hx
  have hact : b.act d.down p = q := by
    have hX := (isSheaf_iff_isSheaf_of_type _ _).mp ((schemeSheaf S).obj X).property
    suffices h : (ULift.up (b.act d.down p) : ULift.{u+1} (T ⟶ X)) = ULift.up q from
      congrArg ULift.down h
    apply (hX R hR).isSeparatedFor
      (fun _ f _ => (⟨f ≫ q⟩ : ((schemeYoneda S).obj X).obj _))
    · intro V f hf
      change (⟨f ≫ b.act d.down p⟩ : ((schemeYoneda S).obj X).obj (op V)) = ⟨f ≫ q⟩
      apply ULift.ext
      rw [b.naturality]
      have hdf : f ≫ d.down = hf.choose := congrArg ULift.down (hd f hf)
      rw [hdf]
      exact hf.choose_spec.symm
    · intro V f hf
      rfl
  exact ⟨d.down, hact, fun c hc => hfree T p (hc.trans hact.symm)⟩

/-- In a free action, equality in any fppf sheaf quotient gives a unique
acting point on the original relative test. -/
theorem existsUnique_act_of_isFppfActionQuotient
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    {Q : FppfSheaf S} {π : (schemeSheaf S).obj X ⟶ Q}
    (hπ : IsFppfActionQuotient b π)
    {T : Over S} (p q : T ⟶ X)
    (hpq : π.hom.app (op T) ⟨p⟩ = π.hom.app (op T) ⟨q⟩) :
    ∃! d : T ⟶ A.X, b.act d p = q :=
  b.existsUnique_act_of_orbitSieve_mem hfree p q
    (ActionQuotientOrbitRelation.orbitSieve_mem b hπ q p hpq.symm)

end SchemeAction

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)

/-- A faithful automorphic action acts freely by inverse precomposition on
every test of an actual isomorphism scheme. -/
theorem actionHom_injective_of_isFaithful (ha : a.IsFaithful)
    (T : Over S) (p : T ⟶ I.parameter) :
    Function.Injective (fun d : T ⟶ A.X => lift d p ≫ I.actionHom a) := by
  intro d e hde
  apply inv_injective
  apply ha d⁻¹ e⁻¹
  intro W t g
  apply (I.universalIso.toFun (t ≫ p)).injective
  have h := congrArg (fun r => I.universalIso.toFun (t ≫ r) g) hde
  simpa only [← Category.assoc, comp_lift, I.actionHom_eval, GrpObj.comp_inv] using h

/-- Construct an outer quotient from a represented fppf sheaf quotient of the
canonical action, with its actual fpqc class morphism. -/
def outerOfFppfActionQuotient (ha : a.IsFaithful)
    (Q : Over S) (c : I.parameter ⟶ Q)
    [Flat c.left] [Surjective c.left] [QuasiCompact c.left]
    (hc : IsFppfActionQuotient (I.modObj a) ((schemeSheaf S).map c)) :
    OuterIsomorphismScheme I a where
  parameter := Q
  classMap := c
  flat := inferInstance
  surjective := inferInstance
  quasiCompact := inferInstance
  invariant T d p := by
    have h := congrArg
      (fun k => k.hom.app (op T) (⟨lift d p⟩ :
        ((schemeYoneda S).obj (A.X ⊗ I.parameter)).obj (op T))) hc.choose
    change (⟨(lift d p ≫ I.actionHom a) ≫ c⟩ :
      ((schemeYoneda S).obj Q).obj (op T)) =
        ⟨(lift d p ≫ snd A.X I.parameter) ≫ c⟩ at h
    simpa only [lift_snd] using congrArg ULift.down h
  orbit T p q hpq :=
    SchemeAction.existsUnique_act_of_isFppfActionQuotient (I.modObj a)
      (I.actionHom_injective_of_isFaithful a ha) hc p q
      (congrArg ULift.up hpq)

end GroupIsomorphismScheme

end Langlands.GroupScheme
