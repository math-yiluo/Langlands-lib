import Langlands.Geometry.FormalGroup.AdicAffineNilpPoints

/-! # Algebra maps for affine formal spectrum points -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.FormalGroup.AdicAffineChart

variable {R : Type u} [CommRing R] {π : R} (C : AdicAffineChart π)

/-- Algebra maps to the discrete test which annihilate a power of the ideal of definition. -/
def ContinuousPoint (B : Nilp.{u, u} R π) :=
  {a : C.algebra →ₐ[R] B.obj // ∃ n : ℕ, C.ideal ^ (n + 1) ≤ RingHom.ker a.toRingHom}

/-- These continuous maps are functorial in the test algebra by postcomposition. -/
def continuousPointFunctor : Nilp.{u, u} R π ⥤ Type u where
  obj := C.ContinuousPoint
  map f := ↾fun a =>
    ⟨f.hom.hom.comp a.val, by
      obtain ⟨n, hn⟩ := a.property
      refine ⟨n, fun x hx => ?_⟩
      change f.hom.hom (a.val x) = 0
      have he : a.val x = 0 := hn hx
      rw [he, map_zero]⟩
  map_id B := by
    apply ConcreteCategory.hom_ext
    intro a
    exact Subtype.ext (AlgHom.id_comp a.val)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact Subtype.ext (AlgHom.comp_assoc _ _ _)

/-- Precompose a quotient point with the actual quotient map. -/
def continuousPointOfQuotient (B : Nilp.{u, u} R π) (n : ℕ) (a : C.quotientTest n ⟶ B) :
    C.ContinuousPoint B :=
  ⟨a.hom.hom.comp (Ideal.Quotient.mkₐ R (C.ideal ^ (n + 1))), ⟨n, fun x hx => by
    change a.hom.hom (Ideal.Quotient.mk (C.ideal ^ (n + 1)) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩⟩

theorem continuousPointOfQuotient_injective (B : Nilp.{u, u} R π) (n : ℕ) :
    Function.Injective (C.continuousPointOfQuotient B n) := by
  intro a b hab
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  exact congrArg Subtype.val hab

/-- An exponent witnessing continuity gives the actual factorization through that quotient. -/
def factorContinuousPoint (B : Nilp.{u, u} R π) (a : C.ContinuousPoint B) (n : ℕ)
    (hn : C.ideal ^ (n + 1) ≤ RingHom.ker a.val.toRingHom) : C.quotientTest n ⟶ B :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    (Ideal.Quotient.liftₐ (C.ideal ^ (n + 1)) a.val (fun _ hx => hn hx)))

@[simp] theorem continuousPointOfQuotient_factor (B : Nilp.{u, u} R π) (a : C.ContinuousPoint B)
    (n : ℕ) (hn : C.ideal ^ (n + 1) ≤ RingHom.ker a.val.toRingHom) :
    C.continuousPointOfQuotient B n (C.factorContinuousPoint B a n hn) = a :=
  Subtype.ext (AlgHom.ext fun _ => rfl)

@[simp] theorem continuousPointOfQuotient_reduce (B : Nilp.{u, u} R π) {m n : ℕ} (i : m ⟶ n)
    (a : C.quotientTest m ⟶ B) :
    C.continuousPointOfQuotient B n (C.quotientReduction i ≫ a) =
      C.continuousPointOfQuotient B m a :=
  Subtype.ext (AlgHom.ext fun _ => rfl)

private def continuousPointCocone : Cocone C.quotientPointDiagram where
  pt := C.continuousPointFunctor
  ι :=
    { app n :=
        { app B := ↾fun a => C.continuousPointOfQuotient B n a
          naturality _ _ f := by
            apply ConcreteCategory.hom_ext
            intro a
            exact Subtype.ext (AlgHom.comp_assoc _ _ _) }
      naturality m n i := by
        apply NatTrans.ext
        funext B
        apply ConcreteCategory.hom_ext
        intro a
        exact C.continuousPointOfQuotient_reduce B i a }

private def continuousPointCoconeIsColimitAt (B : Nilp.{u, u} R π) :
    IsColimit (((evaluation _ _).obj B).mapCocone C.continuousPointCocone) where
  desc s := ↾fun a =>
    s.ι.app a.property.choose (C.factorContinuousPoint B a a.property.choose a.property.choose_spec)
  fac s n := by
    apply ConcreteCategory.hom_ext
    intro a
    let x := C.continuousPointOfQuotient B n a
    let j := x.property.choose
    let b := C.factorContinuousPoint B x j x.property.choose_spec
    let k := max j n
    let i : j ⟶ k := homOfLE (le_max_left j n)
    let h : n ⟶ k := homOfLE (le_max_right j n)
    have he : C.quotientReduction i ≫ b = C.quotientReduction h ≫ a := by
      apply C.continuousPointOfQuotient_injective B k
      rw [continuousPointOfQuotient_reduce, continuousPointOfQuotient_reduce,
        continuousPointOfQuotient_factor]
    have hi : s.ι.app k (C.quotientReduction i ≫ b) = s.ι.app j b :=
      ConcreteCategory.congr_hom (s.w i) b
    have hh : s.ι.app k (C.quotientReduction h ≫ a) = s.ι.app n a :=
      ConcreteCategory.congr_hom (s.w h) a
    change s.ι.app j b = s.ι.app n a
    exact hi.symm.trans ((congrArg (fun y => s.ι.app k y) he).trans hh)
  uniq s f hf := by
    apply ConcreteCategory.hom_ext
    intro a
    let n := a.property.choose
    let b := C.factorContinuousPoint B a n a.property.choose_spec
    have h : f (C.continuousPointOfQuotient B n b) = s.ι.app n b :=
      ConcreteCategory.congr_hom (hf n) b
    rw [continuousPointOfQuotient_factor] at h
    exact h

private def continuousPointColimit : ColimitCocone C.quotientPointDiagram :=
  ⟨C.continuousPointCocone, evaluationJointlyReflectsColimits _ C.continuousPointCoconeIsColimitAt⟩

/-- Points of the affine formal spectrum are exactly the continuous algebra maps to affine tests. -/
def nilpPointsContinuousIso : C.nilpPointsFunctor ≅ C.continuousPointFunctor :=
  colimit.isoColimitCocone C.continuousPointColimit

@[simp] theorem nilpPointsContinuousIso_quotientPoint (B : Nilp.{u, u} R π) (n : ℕ)
    (a : C.quotientTest n ⟶ B) :
    C.nilpPointsContinuousIso.hom.app B ((C.quotientPointInclusion n).app B a) =
      C.continuousPointOfQuotient B n a :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (colimit.isoColimitCocone_ι_hom C.continuousPointColimit n) B) a

end Langlands.FormalGroup.AdicAffineChart
