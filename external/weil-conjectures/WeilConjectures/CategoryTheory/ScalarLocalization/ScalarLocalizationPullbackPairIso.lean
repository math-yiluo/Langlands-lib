/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationRestrictedPairIso
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Localized comparison for a functor composed with a restricted pair operation

Source: blueprint dual-Tate compatibility, Step 5, raw coefficient transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory Opposite TensorProduct
namespace CategoryTheory.ScalarLocalization

private theorem localized_map_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hA
  cases hB
  cases h
  rfl

private theorem restricted_map_heq {C D : Type*} [Category* C] [Category* D]
    (q : ObjectProperty (Cᵒᵖ × C)) (H : q.FullSubcategory ⥤ D)
    {P Q P' Q' : q.FullSubcategory} (hP : P = P') (hQ : Q = Q')
    (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2)
    (a' : Q'.obj.1.unop ⟶ P'.obj.1.unop) (b' : P'.obj.2 ⟶ Q'.obj.2)
    (ha : HEq a a') (hb : HEq b b') :
    HEq (H.map (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom a.op b)))
      (H.map (ObjectProperty.homMk (X := P') (Y := Q') (Prod.mkHom a'.op b'))) := by
  subst P' Q'
  cases ha
  cases hb
  rfl

private def linear_bilinearAdd {R : Type*} [CommSemiring R]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (b : M →ₗ[R] N →ₗ[R] P) :
    M →+ N →+ P := LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom

private def bilinear_post {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (b : M →+ N →+ P) (f : P →+ Q) : M →+ N →+ Q where
  toFun x := f.comp (b x)
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private def bilinear_pre {M N P M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    (b : M →+ N →+ P) (f : M' →+ M) (g : N' →+ N) : M' →+ N' →+ P where
  toFun x := (b (f x)).comp g
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

/-- A comparison between an operation and pullback extends over scalar-localized arrows.
Source: blueprint dual-Tate compatibility, Step 5
(blueprint: lem-pod-localized-pullback-pair-comparison).
Proof: the source composite has the object formula obtained by composing the two
object formulas. The target composite has the same formula because the induced
pair functor sends each underlying integral pair to its integral pullback pair.
Postcompose the source operation's separately linear action with pullback's
additive map. Precompose the target operation's action in both variables with
pullback's additive maps. Their pure-tensor formulas follow respectively from
the operation formula followed by pullback's formula, and from the two pullback
formulas followed by the operation formula. Equality of permitted pairs handles
the different endpoint presentations without assuming their literal equality.
Apply restrictedPairIso_existsUnique to these two separately additive actions.
Its tensor induction supplies naturality on all arrows, including sums and zero;
its component identities prescribe both directions and ensure uniqueness. -/
theorem pullbackPairIso_existsUnique
    {R : Type*} [CommRing R] {C D : Type*}
    [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D] (t : R)
    (q : ObjectProperty (Cᵒᵖ × C))
    (q' : ObjectProperty ((ScalarLocalization R C t)ᵒᵖ × ScalarLocalization R C t))
    (p : ObjectProperty (Dᵒᵖ × D))
    (p' : ObjectProperty ((ScalarLocalization R D t)ᵒᵖ × ScalarLocalization R D t))
    (hq : ∀ A, q' A → q (op A.1.unop.obj, A.2.obj))
    (hp : ∀ A, p' A → p (op A.1.unop.obj, A.2.obj))
    (hpLift : ∀ A : p.FullSubcategory,
      p' (op (ScalarLocalization.mk A.obj.1.unop), ScalarLocalization.mk A.obj.2))
    (F₀ : C ⥤ D) (F : ScalarLocalization R C t ⥤ ScalarLocalization R D t)
    [F.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (mF : ∀ (K N : C) (f : K ⟶ N) (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk N))
        (a ⊗ₜ[R] F₀.map f))
    (H₀ : q.FullSubcategory ⥤ C) (I₀ : p.FullSubcategory ⥤ D)
    (H : q'.FullSubcategory ⥤ ScalarLocalization R C t)
    (I : p'.FullSubcategory ⥤ ScalarLocalization R D t)
    (hH : ∀ A, H.obj A = ⟨H₀.obj
      ⟨(op A.obj.1.unop.obj, A.obj.2.obj), hq _ A.property⟩⟩)
    (hI : ∀ A, I.obj A = ⟨I₀.obj
      ⟨(op A.obj.1.unop.obj, A.obj.2.obj), hp _ A.property⟩⟩)
    (mH : ∀ P Q : q'.FullSubcategory,
      ∃ β : (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[Localization.Away t]
          (P.obj.2 ⟶ Q.obj.2) →ₗ[Localization.Away t] (H.obj P ⟶ H.obj Q),
        (∀ a b, H.map (ObjectProperty.homMk (Prod.mkHom a.op b)) = β a b) ∧
        ∀ a b (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b))
            ((x * y) ⊗ₜ[R] H₀.map (ObjectProperty.homMk
              (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩)
              (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hq _ Q.property⟩)
              (Prod.mkHom a.op b))))
    (mI : ∀ P Q : p'.FullSubcategory,
      ∃ β : (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[Localization.Away t]
          (P.obj.2 ⟶ Q.obj.2) →ₗ[Localization.Away t] (I.obj P ⟶ I.obj Q),
        (∀ a b, I.map (ObjectProperty.homMk (Prod.mkHom a.op b)) = β a b) ∧
        ∀ a b (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b))
            ((x * y) ⊗ₜ[R] I₀.map (ObjectProperty.homMk
              (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hp _ P.property⟩)
              (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hp _ Q.property⟩)
              (Prod.mkHom a.op b))))
    (permitted₀ : ∀ A : q.FullSubcategory,
      p (op (F₀.obj A.obj.1.unop), F₀.obj A.obj.2))
    (permitted : ∀ A : q'.FullSubcategory,
      p' (op (F.obj A.obj.1.unop), F.obj A.obj.2)) :
    let pair₀ := p.lift (q.ι ⋙ F₀.op.prod F₀) permitted₀
    let pair := p'.lift (q'.ι ⋙ F.op.prod F) permitted
    ∀ α : H₀ ⋙ F₀ ≅ pair₀ ⋙ I₀,
    ∃! β : H ⋙ F ≅ pair ⋙ I, ∀ A,
      HEq (β.hom.app A) ((ScalarLocalization.localization R D t).map
        (α.hom.app ⟨(op A.obj.1.unop.obj, A.obj.2.obj), hq _ A.property⟩)) ∧
      HEq (β.inv.app A) ((ScalarLocalization.localization R D t).map
        (α.inv.app ⟨(op A.obj.1.unop.obj, A.obj.2.obj), hq _ A.property⟩)) := by
  intro pair₀ pair α
  let integral (A : q'.FullSubcategory) : q.FullSubcategory :=
    ⟨(op A.obj.1.unop.obj, A.obj.2.obj), hq _ A.property⟩
  let integral' (A : p'.FullSubcategory) : p.FullSubcategory :=
    ⟨(op A.obj.1.unop.obj, A.obj.2.obj), hp _ A.property⟩
  have hpair (A : q'.FullSubcategory) :
      integral' (pair.obj A) = pair₀.obj (integral A) := by
    apply ObjectProperty.FullSubcategory.ext
    change (op (F.obj A.obj.1.unop).obj, (F.obj A.obj.2).obj) = _
    rw [hF, hF]
    rfl
  have hleft (A : q'.FullSubcategory) :
      (H ⋙ F).obj A = ⟨(H₀ ⋙ F₀).obj (integral A)⟩ := by
    change F.obj (H.obj A) = _
    rw [hF, hH]
    rfl
  have hright (A : q'.FullSubcategory) :
      (pair ⋙ I).obj A = ⟨(pair₀ ⋙ I₀).obj (integral A)⟩ := by
    change I.obj _ = _
    rw [hI]
    change ScalarLocalization.mk (I₀.obj (integral' (pair.obj A))) = _
    rw [hpair]
    rfl
  apply restrictedPairIso_existsUnique t q q' hq
    (H₀ ⋙ F₀) (pair₀ ⋙ I₀) α (H ⋙ F) (pair ⋙ I) hleft hright
  · intro P Q
    obtain ⟨β, hβ, pβ⟩ := mH P Q
    refine ⟨bilinear_post (linear_bilinearAdd β) F.mapAddHom, ?_, ?_⟩
    · intro a b
      exact congrArg F.map (hβ a b)
    · intro a b x y
      let f : integral P ⟶ integral Q := ObjectProperty.homMk (Prod.mkHom a.op b)
      exact (localized_map_heq F (hH _) (hH _) (pβ a b x y)).trans
        (mF _ _ (H₀.map f) (x * y))
  · intro P Q
    obtain ⟨β, hβ, pβ⟩ := mI (pair.obj P) (pair.obj Q)
    refine ⟨bilinear_pre (linear_bilinearAdd β) F.mapAddHom F.mapAddHom, ?_, ?_⟩
    · intro a b
      exact hβ (F.map a) (F.map b)
    · intro a b x y
      change HEq (β (F.map _) (F.map _)) _
      refine (heq_of_eq (hβ (F.map (x ⊗ₜ[R] a)) (F.map (y ⊗ₜ[R] b))).symm).trans ?_
      let liftPair (A : p.FullSubcategory) : p'.FullSubcategory :=
        ⟨(op (ScalarLocalization.mk A.obj.1.unop), ScalarLocalization.mk A.obj.2), hpLift A⟩
      let P' := liftPair (pair₀.obj (integral P))
      let Q' := liftPair (pair₀.obj (integral Q))
      have hP : pair.obj P = P' := by
        apply ObjectProperty.FullSubcategory.ext
        change (op (F.obj P.obj.1.unop), F.obj P.obj.2) = _
        rw [hF, hF]
        rfl
      have hQ : pair.obj Q = Q' := by
        apply ObjectProperty.FullSubcategory.ext
        change (op (F.obj Q.obj.1.unop), F.obj Q.obj.2) = _
        rw [hF, hF]
        rfl
      have hmap := restricted_map_heq p' I hP hQ
        (F.map (x ⊗ₜ[R] a)) (F.map (y ⊗ₜ[R] b))
        (x ⊗ₜ[R] F₀.map a) (y ⊗ₜ[R] F₀.map b)
        (mF _ _ a x) (mF _ _ b y)
      obtain ⟨δ, hδ, pδ⟩ := mI P' Q'
      have hd := pδ (F₀.map a) (F₀.map b) x y
      exact hmap.trans ((heq_of_eq (hδ _ _)).trans hd)

end CategoryTheory.ScalarLocalization
