/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Basic

/-!
# Invariant open subschemes for a descent datum

Let `p : X ⟶ Y` be a morphism of schemes and `D` a descent datum on a scheme `V` over `X`
relative to `p`. We introduce

- the universal transport `D.univ : V ×_Y X ⟶ V`, which determines every transport of `D`
  (`CategoryTheory.Over.DescentDatum.transport_left_eq`);
- invariant open subschemes `U ⊆ V`: transports of points of `U` are points of `U`
  (`CategoryTheory.Over.DescentDatum.IsInvariant`);
- the restriction `D.restrict U hU` of `D` to an invariant open subscheme `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} (D : DescentDatum p V)

/-- The **universal transport** `V ×_Y X ⟶ V` of a descent datum: the transport of the first
projection, a point of `V` over `V ×_Y X ⟶ V ⟶ X`, to a point of `V` over the second projection.
-/
noncomputable def univ : Limits.pullback (V.hom ≫ p) p ⟶ V.left :=
  (D.transport (pullback.fst (V.hom ≫ p) p ≫ V.hom) (pullback.snd (V.hom ≫ p) p)
    (by rw [Category.assoc, pullback.condition])
    (Over.homMk (pullback.fst (V.hom ≫ p) p) rfl)).left

@[reassoc (attr := simp)]
lemma univ_hom : D.univ ≫ V.hom = pullback.snd (V.hom ≫ p) p :=
  Over.w (D.transport _ _ _ _)

/-- Every transport is a pullback of the universal transport. -/
lemma transport_left_eq {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) :
    (D.transport f₁ f₂ h a).left =
      pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h) ≫ D.univ :=
  D.transport_left_eq_comp _ _ _ _ _ _ (by simp) (by simp) _ (by simp)

/-- The universal transport of the universal point is the identity. -/
@[reassoc (attr := simp)]
lemma lift_univ :
    pullback.lift (𝟙 V.left) V.hom (by simp) ≫ D.univ = 𝟙 V.left := by
  have := D.transport_left_eq V.hom V.hom rfl (𝟙 _)
  rw [D.transport_self] at this
  exact this.symm

/-- An open subscheme `U` of `V` is **invariant** under the descent datum `D` if the transport of
a point of `V` lying in `U` lies in `U`. -/
def IsInvariant (U : V.left.Opens) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
    Set.range a.left ⊆ U → Set.range (D.transport f₁ f₂ h a).left ⊆ U

/-- Invariance can be checked on the universal transport. -/
lemma isInvariant_iff (U : V.left.Opens) :
    D.IsInvariant U ↔ ∀ z, pullback.fst (V.hom ≫ p) p z ∈ U → D.univ z ∈ U := by
  refine ⟨fun hU z hz ↦ ?_, fun hU T f₁ f₂ h a ha ↦ ?_⟩
  · let W := (pullback.fst (V.hom ≫ p) p) ⁻¹ᵁ U
    have hr := hU (W.ι ≫ pullback.fst _ _ ≫ V.hom) (W.ι ≫ pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition])
      (Over.homMk (W.ι ≫ pullback.fst _ _) (by simp)) (by
        rintro _ ⟨w, rfl⟩
        exact w.2)
    have e : (D.transport (W.ι ≫ pullback.fst _ _ ≫ V.hom) (W.ι ≫ pullback.snd _ _)
        (by rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition])
        (Over.homMk (W.ι ≫ pullback.fst _ _) (by simp))).left = W.ι ≫ D.univ :=
      D.transport_left_eq_comp _ _ _ _ _ _ (by simp) rfl _ rfl
    rw [e] at hr
    exact hr ⟨⟨z, hz⟩, rfl⟩
  · rw [D.transport_left_eq]
    rintro _ ⟨t, rfl⟩
    refine hU _ ?_
    have := ha ⟨t, rfl⟩
    rwa [← pullback.lift_fst a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h),
      Scheme.Hom.comp_apply] at this

lemma isInvariant_top : D.IsInvariant ⊤ := fun _ _ _ _ _ _ ↦ by simp


lemma IsInvariant.inf {U U' : V.left.Opens} (hU : D.IsInvariant U) (hU' : D.IsInvariant U') :
    D.IsInvariant (U ⊓ U') := fun _ f₁ f₂ h a ha ↦
  Set.subset_inter (hU f₁ f₂ h a (ha.trans Set.inter_subset_left))
    (hU' f₁ f₂ h a (ha.trans Set.inter_subset_right))

variable {D}

/-- The transport of a point of the invariant open subscheme `U`, as a point of `U`. -/
noncomputable def restrictTransport {U : V.left.Opens} (hU : D.IsInvariant U) {T : Scheme.{u}}
    (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
    T ⟶ U :=
  IsOpenImmersion.lift U.ι
    (D.transport f₁ f₂ h (Over.homMk (a.left ≫ U.ι) (by simpa using Over.w a))).left (by
      rw [Scheme.Opens.range_ι]
      refine hU _ _ _ _ ?_
      rintro _ ⟨t, rfl⟩
      exact (a.left t).2)

@[reassoc (attr := simp)]
lemma restrictTransport_ι {U : V.left.Opens} (hU : D.IsInvariant U) {T : Scheme.{u}}
    (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
    restrictTransport hU f₁ f₂ h a ≫ U.ι =
      (D.transport f₁ f₂ h (Over.homMk (a.left ≫ U.ι) (by simpa using Over.w a))).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The transport of a point of the invariant open subscheme `U`, as a point of `U` over `f₂`. -/
noncomputable def restrictTransportHom {U : V.left.Opens} (hU : D.IsInvariant U)
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) : Over.mk f₂ ⟶ Over.mk (U.ι ≫ V.hom) :=
  Over.homMk (restrictTransport hU f₁ f₂ h a) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, restrictTransport_ι]
    exact Over.w (D.transport _ _ _ _))

@[reassoc (attr := simp)]
lemma restrictTransportHom_left_ι {U : V.left.Opens} (hU : D.IsInvariant U) {T : Scheme.{u}}
    (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
    (restrictTransportHom hU f₁ f₂ h a).left ≫ U.ι =
      (D.transport f₁ f₂ h (Over.homMk (a.left ≫ U.ι) (by simpa using Over.w a))).left :=
  restrictTransport_ι hU f₁ f₂ h a

variable (D) in
/-- The **restriction** of a descent datum to an invariant open subscheme. -/
noncomputable def restrict (U : V.left.Opens) (hU : D.IsInvariant U) :
    DescentDatum p (Over.mk (U.ι ≫ V.hom)) where
  transport := restrictTransportHom hU
  transport_homMk_comp g f₁ f₂ h a := by
    refine Over.OverMorphism.ext ((cancel_mono U.ι).mp ?_)
    refine (restrictTransportHom_left_ι hU _ _ _ _).trans
      ((D.transport_left_eq_comp g f₁ f₂ h (Over.homMk (a.left ≫ U.ι) (by simpa using Over.w a))
        _ rfl rfl _ (by simp)).trans ?_)
    simp only [Over.comp_left, Category.assoc, restrictTransportHom_left_ι, Over.homMk_left]
  transport_self f a := by
    refine Over.OverMorphism.ext ((cancel_mono U.ι).mp ?_)
    refine (restrictTransportHom_left_ι hU _ _ _ _).trans ?_
    rw [D.transport_self]
    rfl
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ a := by
    refine Over.OverMorphism.ext ((cancel_mono U.ι).mp ?_)
    refine (restrictTransportHom_left_ι hU _ _ _ _).trans ?_
    refine (D.transport_left_congr' h₂₃ h₂₃ rfl rfl
      (D.transport f₁ f₂ h₁₂ (Over.homMk (a.left ≫ U.ι) (by simpa using Over.w a))) _
      (restrictTransportHom_left_ι hU f₁ f₂ h₁₂ a)).trans ?_
    rw [D.transport_transport, restrictTransportHom_left_ι]

@[reassoc (attr := simp)]
lemma restrict_transport_left_ι (U : V.left.Opens) (hU : D.IsInvariant U) {T : Scheme.{u}}
    (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
    ((D.restrict U hU).transport f₁ f₂ h a).left ≫ U.ι =
      (D.transport f₁ f₂ h (Over.homMk (a.left ≫ U.ι) (by simpa using Over.w a))).left :=
  restrictTransportHom_left_ι hU f₁ f₂ h a

end CategoryTheory.Over.DescentDatum
