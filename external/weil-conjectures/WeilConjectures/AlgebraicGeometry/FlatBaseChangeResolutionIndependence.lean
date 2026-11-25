/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # FlatBaseChangeResolutionIndependence

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

-- The usual comparison homotopy only needs injectivity of the target terms,
-- not exactness of the target complex (Stacks, Derived Categories, Tag 013S).
private lemma augmentedHomotopy {C : Type*} [Category C] [Abelian C]
    {F : C} (I : InjectiveResolution F) (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (a b : I.cocomplex ⟶ K)
    (h : I.ι.f 0 ≫ a.f 0 = I.ι.f 0 ≫ b.f 0) : Nonempty (Homotopy a b) := by
  let e := a - b
  have he : I.ι.f 0 ≫ e.f 0 = 0 := by
    dsimp [e]
    rw [Preadditive.comp_sub, h, sub_self]
  let s₀ := I.exact₀.descToInjective (e.f 0) he
  have hs₀ : I.cocomplex.d 0 1 ≫ s₀ = e.f 0 :=
    I.exact₀.comp_descToInjective _ _
  have h₁ : I.cocomplex.d 0 1 ≫ (e.f 1 - s₀ ≫ K.d 0 1) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hs₀, e.comm, sub_self]
  let s₁ := (I.exact_succ 0).descToInjective (e.f 1 - s₀ ≫ K.d 0 1) h₁
  have hs₁ : I.cocomplex.d 1 2 ≫ s₁ = e.f 1 - s₀ ≫ K.d 0 1 :=
    (I.exact_succ 0).comp_descToInjective _ _
  apply Nonempty.intro
  apply Homotopy.equivSubZero.invFun
  refine Homotopy.mkCoinductive e s₀ hs₀.symm s₁ ?_ ?_
  · rw [hs₁, add_sub_cancel]
  · intro n q
    obtain ⟨s, s', hs⟩ := q
    have hz : I.cocomplex.d (n + 1) (n + 2) ≫
        (e.f (n + 2) - s' ≫ K.d (n + 1) (n + 2)) = 0 := by
      rw [Preadditive.comp_sub, ← e.comm, hs, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d,
        comp_zero, zero_add, sub_self]
    refine ⟨(I.exact_succ (n + 1)).descToInjective _ hz, ?_⟩
    rw [(I.exact_succ (n + 1)).comp_descToInjective, add_sub_cancel]

/-- Resolution comparison and homotopy invariance of the flat base-change morphism.
Source: Stacks, Cohomology, Tag 02N7 and Derived Categories, Tags 013P, 013S.
(blueprint: lem-weil-pbc-flat-base-change-resolution-independence).

Proof: Compare I and I₁ by lifts of the identity of F, and J and J₁ by lifts of
 the identity of g'^*F. Their composites are homotopic to identities. Pushforward
 preserves injectives because g' is flat. The two augmented maps into the pushed
 target resolution are homotopic by uniqueness of lifts. Apply f_*, the square
 isomorphism, and the termwise adjunction; these preserve homotopies. Homology
 identifies the two resulting maps. Naturality of the exact pullback homology
 comparison and of isoRightDerivedObj cancels the resolution comparisons, giving
 the asserted equality on the fixed derived objects. -/
theorem flatBaseChangeResolutionBeta_independent {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (I₁ : InjectiveResolution F)
    (J₁ : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t₁ : I₁.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J₁.cocomplex)
    (ht₁ : I₁.ι.f 0 ≫ t₁.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J₁.ι.f 0))
    (p : ℕ) :
    flatBaseChangeResolutionBeta f g I J t p =
      flatBaseChangeResolutionBeta f g I₁ J₁ t₁ p := by
  let a := (I.homotopyEquiv I₁).hom
  let b := (J.homotopyEquiv J₁).hom
  let R := (pushforward (pullback.snd g f)).mapHomologicalComplex (ComplexShape.up ℕ)
  have ha : I.ι.f 0 ≫ a.f 0 = I₁.ι.f 0 := by
    simpa only [a, HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom (I.homotopyEquiv_hom_ι I₁) 0
  have hb : J.ι.f 0 ≫ b.f 0 = J₁.ι.f 0 := by
    simpa only [b, HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom (J.homotopyEquiv_hom_ι J₁) 0
  have : (pushforward (pullback.snd g f)).PreservesInjectiveObjects :=
    (flat_module_pullback_exact_pushforward_injective (pullback.snd g f)).2
  have : ∀ n, Injective ((R.obj J₁.cocomplex).X n) := fun n ↦ by
    change Injective ((pushforward (pullback.snd g f)).obj (J₁.cocomplex.X n))
    infer_instance
  obtain ⟨h⟩ := augmentedHomotopy I (R.obj J₁.cocomplex)
    (t ≫ R.map b) (a ≫ t₁) (by
      simp only [HomologicalComplex.comp_f, R, Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ht, Category.assoc, ← Functor.map_comp, hb,
        ← Category.assoc, ha, ht₁])
  let P := (pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)
  let T := (pushforward (pullback.fst g f)).mapHomologicalComplex (ComplexShape.up ℕ)
  let G := (pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)
  let L := (tensorPullback g).mapHomologicalComplex (ComplexShape.up ℕ)
  let e : R ⋙ P ≅ T ⋙ G := NatIso.mapHomologicalComplex (flatBaseChangePushforwardSquare f g)
    (ComplexShape.up ℕ)
  have hq : Homotopy
      (flatBaseChangeResolutionQ f g I J t ≫ G.map (T.map b))
      (P.map a ≫ flatBaseChangeResolutionQ f g I₁ J₁ t₁) := by
    have h' := ((pushforward f).mapHomotopy h).compRight (e.hom.app J₁.cocomplex)
    have he : P.map (R.map b) ≫ e.hom.app J₁.cocomplex =
        e.hom.app J.cocomplex ≫ G.map (T.map b) := e.hom.naturality b
    have hleft : P.map (t ≫ R.map b) ≫ e.hom.app J₁.cocomplex =
        flatBaseChangeResolutionQ f g I J t ≫ G.map (T.map b) := by
      rw [Functor.map_comp, Category.assoc, he, ← Category.assoc]
      rfl
    have hright : P.map (a ≫ t₁) ≫ e.hom.app J₁.cocomplex =
        P.map a ≫ flatBaseChangeResolutionQ f g I₁ J₁ t₁ := by
      rw [Functor.map_comp, Category.assoc]
      rfl
    rw [hleft, hright] at h'
    exact h'
  let adj := (Classical.choose (exists_tensorPullbackAdjunction g)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have hc : Homotopy
      (flatBaseChangeResolutionC f g I J t ≫ T.map b)
      (L.map (P.map a) ≫ flatBaseChangeResolutionC f g I₁ J₁ t₁) := by
    have h' := ((tensorPullback g).mapHomotopy hq).compRight
      (adj.counit.app (T.obj J₁.cocomplex))
    change Homotopy ((adj.homEquiv _ _).symm
      (flatBaseChangeResolutionQ f g I J t) ≫ T.map b)
      (L.map (P.map a) ≫ (adj.homEquiv _ _).symm
        (flatBaseChangeResolutionQ f g I₁ J₁ t₁))
    rw [← adj.homEquiv_naturality_right_symm,
      ← adj.homEquiv_naturality_left_symm]
    exact h'
  let H := HomologicalComplex.homologyFunctor S'.Modules (ComplexShape.up ℕ) p
  let H₀ := HomologicalComplex.homologyFunctor S.Modules (ComplexShape.up ℕ) p
  have hi : (I₁.isoRightDerivedObj (pushforward f) p).hom =
      (I.isoRightDerivedObj (pushforward f) p).hom ≫ H₀.map (P.map a) := by
    have hi' := InjectiveResolution.isoRightDerivedObj_hom_naturality
      (𝟙 F) I I₁ a (by simpa only [Category.id_comp] using ha) (pushforward f) p
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at hi'
    exact hi'
  have hj : H.map (T.map b) ≫
      (J₁.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv =
      (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv := by
    have hj' := InjectiveResolution.isoRightDerivedObj_inv_naturality
      (𝟙 _) J J₁ b (by simpa only [Category.id_comp] using hb)
      (pushforward (pullback.fst g f)) p
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at hj'
    exact hj'.symm
  have hn : (tensorPullback g).map (H₀.map (P.map a)) ≫
      (((P.obj I₁.cocomplex).sc p).mapHomologyIso (tensorPullback g)).inv =
      (((P.obj I.cocomplex).sc p).mapHomologyIso (tensorPullback g)).inv ≫
        H.map (L.map (P.map a)) := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor S.Modules (ComplexShape.up ℕ) p).map
        (P.map a)) (tensorPullback g)
  have hh : H.map (flatBaseChangeResolutionC f g I J t) ≫ H.map (T.map b) =
      H.map (L.map (P.map a)) ≫ H.map (flatBaseChangeResolutionC f g I₁ J₁ t₁) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact hc.homologyMap_eq p
  unfold flatBaseChangeResolutionBeta
  rw [hi, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((tensorPullback g).map (H₀.map (P.map a))), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (H.map (L.map (P.map a))), ← hh]
  simp only [Category.assoc]
  rw [hj]

end AlgebraicGeometry.Scheme.Modules
