/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeCoordinatesNaturality
import WeilConjectures.AlgebraicGeometry.Modules.StructureBaseChangeSectionsNaturality
import WeilConjectures.AlgebraicGeometry.Modules.CanonicalStructureBaseChangeIsIso
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSectionFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Canonical affine base change of finite étale section coordinates

## References

* Stacks Project, Tag 02KG, with the naturality of the affine tensor comparison
* Stacks Project, Tag 02KG, affine base change, and Tag 0EKP, restriction of the finite free
  embedding to infinitesimal neighbourhoods
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale)

/-- The structure morphism of the cover over the thickened base open. -/
def coverToBase (n : ℕ) : cover f V P n ⟶ Limits.pullback V.ι (baseMap f n) :=
  pullback.lift (coverMap f V P n ≫ P.obj.hom) (pullback.snd _ _)
    (by simp only [Category.assoc, coverMap]; exact pullback.condition)

/-- The canonical comparison from the pulled-back finite algebra to the thickened cover's
structure sheaf, adjoint to restriction of functions along `coverMap`. -/
def pushforwardComparison (n : ℕ) :
    (Modules.pullback (pullback.fst V.ι (baseMap f n))).obj
        ((Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)) ⟶
      (Modules.pushforward (coverToBase f V P n)).obj (Modules.unit (cover f V P n)) :=
  ((Modules.pullbackPushforwardAdjunction (pullback.fst V.ι (baseMap f n))).homEquiv _ _).symm
    ((Modules.pushforward P.obj.hom).map
        (unitToPushforwardObjUnit (coverMap f V P n).toRingCatSheafHom) ≫
      (Modules.pushforwardComp (coverMap f V P n) P.obj.hom).hom.app _ ≫
      (Modules.pushforwardCongr
        (by simp [coverToBase])).hom.app _ ≫
      (Modules.pushforwardComp (coverToBase f V P n)
        (pullback.fst V.ι (baseMap f n))).inv.app _)

/-- The inverse on sections of the canonical affine base-change comparison. -/
def liftSection (n : ℕ) (a : Γ(cover f V P n, ⊤)) :
    Γ((Modules.pullback (pullback.fst V.ι (baseMap f n))).obj
      ((Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)), ⊤) :=
  Function.invFun ((pushforwardComparison f V P n).app ⊤) a

/-- Coordinates of a lifted section with respect to a morphism `α` from the direct image to a
finite free module. -/
def coordinates {r : ℕ}
    (α : (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left) ⟶
      free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
    (n : ℕ) (a : Γ(cover f V P n, ⊤)) :
    Fin r → Γ(Limits.pullback V.ι (baseMap f n), ⊤) :=
  fun i ↦ Modules.freeSectionsEquiv (ULift.{u} (Fin r))
    (((Modules.pullback (pullback.fst V.ι (baseMap f n))).map α ≫
      (Modules.pullbackFreeIso (pullback.fst V.ι (baseMap f n))
        (ULift.{u} (Fin r))).hom).app ⊤ (liftSection f V P n a)) (ULift.up i)

set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinates of a lifted section are compatible with the transition maps between
successive thickenings (as an equality of functions). -/
theorem pushforward_coordinates_transition_fun :
    ∀ (r : ℕ)
      (α : (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left) ⟶
        free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))),
      (∀ (n : ℕ) (a : Γ(cover f V P (n + 1), ⊤)),
        coordinates f V P α n ((coverTransition f V P n).appTop a) =
          fun i ↦
            (pullback.lift (pullback.fst V.ι (baseMap f n))
              (pullback.snd V.ι (baseMap f n) ≫ baseTransition f n)
              (by rw [Category.assoc, baseTransition_comp_baseMap]
                  exact pullback.condition)).appTop
                (coordinates f V P α (n + 1) a i)) := by
  intro r α n a
  let v := pullback.lift (pullback.fst V.ι (baseMap f n))
    (pullback.snd V.ι (baseMap f n) ≫ baseTransition f n)
    (by rw [Category.assoc, baseTransition_comp_baseMap]; exact pullback.condition)
  have hv : v ≫ pullback.fst V.ι (baseMap f (n + 1)) =
      pullback.fst V.ι (baseMap f n) := by simp [v]
  have : IsFinite P.obj.hom := P.property
  have hbc (m : ℕ) : Function.Bijective ((pushforwardComparison f V P m).app ⊤) := by
    have sq : IsPullback (coverMap f V P m) (coverToBase f V P m) P.obj.hom
        (pullback.fst V.ι (baseMap f m)) := by
      refine IsPullback.of_bot ?_ (by simp [coverToBase])
        (IsPullback.of_hasPullback V.ι (baseMap f m))
      simpa only [coverToBase, pullback.lift_snd, coverMap, cover] using
        (IsPullback.of_hasPullback (P.obj.hom ≫ V.ι) (baseMap f m))
    have : IsIso (pushforwardComparison f V P m) :=
      Modules.canonical_structure_baseChange_isIso P.obj.hom (coverToBase f V P m)
        (pullback.fst V.ι (baseMap f m)) (coverMap f V P m) sq
    exact ConcreteCategory.bijective_of_isIso _
  have hb0c := hbc n
  have hb1c := hbc (n + 1)
  generalize hb0 : pushforwardComparison f V P n = b0 at hb0c
  generalize hb1 : pushforwardComparison f V P (n + 1) = b1 at hb1c
  obtain ⟨x, hx⟩ := hb1c.surjective a
  let y := Modules.pullbackSectionFactorization
    (pullback.fst V.ι (baseMap f (n + 1))) (pullback.fst V.ι (baseMap f n)) v hv
    ((Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)) x
  have hy : Modules.Hom.app b0 ⊤ y = (coverTransition f V P n).appTop a := by
    have hw : coverTransition f V P n ≫ coverToBase f V P (n + 1) =
        coverToBase f V P n ≫ v := by
      apply pullback.hom_ext <;> simp [coverToBase, coverTransition, v, coverMap,
        Category.assoc]
    have hn := @Modules.structure_baseChange_sections_naturality
      P.obj.left V.toScheme (cover f V P (n + 1))
      (Limits.pullback V.ι (baseMap f (n + 1)))
      (cover f V P n) (Limits.pullback V.ι (baseMap f n)) P.obj.hom
      (coverToBase f V P (n + 1)) (coverToBase f V P n)
      (pullback.fst V.ι (baseMap f (n + 1))) (pullback.fst V.ι (baseMap f n))
      (coverMap f V P (n + 1)) (coverMap f V P n)
      (by simp [coverToBase]) (by simp [coverToBase])
      v (coverTransition f V P n) hv (coverTransition_coverMap f V P n) hw
      b1 b0 hb1.symm hb0.symm x a hx
    exact hn
  have hl0 : liftSection f V P n (Modules.Hom.app b0 ⊤ y) = y := by
    unfold liftSection
    rw [hb0]
    exact Function.leftInverse_invFun hb0c.injective y
  have hl : liftSection f V P n ((coverTransition f V P n).appTop a) = y :=
    (congrArg (liftSection f V P n) hy.symm).trans hl0
  have hl1 : liftSection f V P (n + 1) a = x := by
    unfold liftSection
    rw [hb1, ← hx]
    exact Function.leftInverse_invFun hb1c.injective x
  funext i
  have hc := Modules.pullback_free_coordinates_naturality
    (pullback.fst V.ι (baseMap f (n + 1))) (pullback.fst V.ι (baseMap f n))
    v hv ((Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)) r α x i
  let c0 := fun z ↦ Modules.freeSectionsEquiv (ULift.{u} (Fin r))
    (((Modules.pullback (pullback.fst V.ι (baseMap f n))).map α ≫
      (Modules.pullbackFreeIso (pullback.fst V.ι (baseMap f n))
        (ULift.{u} (Fin r))).hom).app ⊤ z) (ULift.up i)
  let c1 := fun z ↦ v.appTop (Modules.freeSectionsEquiv (ULift.{u} (Fin r))
    (((Modules.pullback (pullback.fst V.ι (baseMap f (n + 1)))).map α ≫
      (Modules.pullbackFreeIso (pullback.fst V.ι (baseMap f (n + 1)))
        (ULift.{u} (Fin r))).hom).app ⊤ z) (ULift.up i))
  exact (congrArg c0 hl).trans (hc.trans (congrArg c1 hl1.symm))

/-- Coordinates from the canonical finite affine base-change comparison are natural
under successive thickenings. -/
theorem pushforward_coordinates_transition :
    ∀ (r : ℕ)
      (α : (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left) ⟶
        free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))),
      (∀ (n : ℕ) (a : Γ(cover f V P (n + 1), ⊤)) (i : Fin r),
        coordinates f V P α n ((coverTransition f V P n).appTop a) i =
          (pullback.lift (pullback.fst V.ι (baseMap f n))
            (pullback.snd V.ι (baseMap f n) ≫ baseTransition f n)
            (by rw [Category.assoc, baseTransition_comp_baseMap]
                exact pullback.condition)).appTop
                  (coordinates f V P α (n + 1) a i)) := by
  intro r α n a i
  exact congrFun (pushforward_coordinates_transition_fun f V P r α n a) i

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
