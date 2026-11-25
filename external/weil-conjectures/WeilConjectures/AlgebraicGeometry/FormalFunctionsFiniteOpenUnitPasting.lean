/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback

/-! # Finite open coefficient-map compatibility

Source: Stacks Project, Tags 02OD, 01F7 and 01FB: factorization of finite
neighbourhoods and restriction of the underlying sheaf maps.
(blueprint: lem-weil-pbc-formal-functions-finite-open-unit-pasting)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pushforwardCongr_symm_comp {Z X : Scheme.{u}} {i k : Z ⟶ X}
    (h : k = i) (N : Z.Modules) :
    (Scheme.Modules.pushforwardCongr h.symm).hom.app N ≫
      (Scheme.Modules.pushforwardCongr h).hom.app N = 𝟙 _ := by
  subst i
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    eqToHom_refl, op_id, Scheme.Modules.Hom.id_app]
  change N.presheaf.map (𝟙 _) ≫ N.presheaf.map (𝟙 _) = 𝟙 _
  exact (congrArg (fun t ↦ t ≫ t) (N.presheaf.map_id _)).trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pushforward_restriction_coherence
    {Z Y X Z₀ Y₀ X₀ : Scheme.{u}} (j : Z ⟶ Y) (g : Y ⟶ X) (i : Z ⟶ X)
    (a : Z₀ ⟶ Z) (b : Y₀ ⟶ Y) (c : X₀ ⟶ X)
    (r : Z₀ ⟶ Y₀) (s : Y₀ ⟶ X₀) (q : Z₀ ⟶ X₀)
    (hj : j ≫ g = i) (hr : r ≫ b = a ≫ j) (hs : s ≫ c = b ≫ g)
    (hq : q ≫ c = a ≫ i) (hrs : r ≫ s = q) (N : Z₀.Modules) :
    let A := Scheme.Modules.pushforwardComp s c ≪≫ Scheme.Modules.pushforwardCongr hs ≪≫
      (Scheme.Modules.pushforwardComp b g).symm
    let B := Scheme.Modules.pushforwardComp r b ≪≫ Scheme.Modules.pushforwardCongr hr ≪≫
      (Scheme.Modules.pushforwardComp a j).symm
    let C := Scheme.Modules.pushforwardComp q c ≪≫ Scheme.Modules.pushforwardCongr hq ≪≫
      (Scheme.Modules.pushforwardComp a i).symm
    let P := Scheme.Modules.pushforwardComp j g ≪≫ Scheme.Modules.pushforwardCongr hj
    let Q := Scheme.Modules.pushforwardComp r s ≪≫ Scheme.Modules.pushforwardCongr hrs
    (Scheme.Modules.pushforward c).map (Q.hom.app N) ≫ C.hom.app N =
      A.hom.app ((Scheme.Modules.pushforward r).obj N) ≫
        (Scheme.Modules.pushforward g).map (B.hom.app N) ≫
          P.hom.app ((Scheme.Modules.pushforward a).obj N) := by
  dsimp only
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  change N.presheaf.map _ ≫ N.presheaf.map _ =
    N.presheaf.map _ ≫ N.presheaf.map _ ≫ N.presheaf.map _
  simp only [← Functor.map_comp, ← op_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem paste_units
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (c : D₀ ⥤ C₀) (b : D₁ ⥤ C₁) (a : D₂ ⥤ C₂)
    (g : C₁ ⥤ C₀) (j : C₂ ⥤ C₁) (i : C₂ ⥤ C₀)
    (s : D₁ ⥤ D₀) (r : D₂ ⥤ D₁) (q : D₂ ⥤ D₀)
    (A : s ⋙ c ≅ b ⋙ g) (B : r ⋙ b ≅ a ⋙ j)
    (C : q ⋙ c ≅ a ⋙ i) (P : j ⋙ g ≅ i) (Q : r ⋙ s ≅ q)
    {F : C₀} {F' : C₁} {Fₙ : C₂} {L : D₀} {M : D₁} {N : D₂}
    (u : F ⟶ c.obj L) (v : F ⟶ g.obj F') (w : F' ⟶ b.obj M)
    (t : F ⟶ i.obj Fₙ) (z : Fₙ ⟶ a.obj N)
    (ψ : L ⟶ s.obj M) (τ : M ⟶ r.obj N) (δ : L ⟶ q.obj N)
    (φ : F' ⟶ j.obj Fₙ)
    (hE : u ≫ c.map ψ ≫ A.hom.app M = v ≫ g.map w)
    (hB : w ≫ b.map τ ≫ B.hom.app N = φ ≫ j.map z)
    (hD : u ≫ c.map δ ≫ C.hom.app N = t ≫ i.map z)
    (hP : v ≫ g.map φ ≫ P.hom.app Fₙ = t)
    (hcoh : c.map (Q.hom.app N) ≫ C.hom.app N =
      A.hom.app (r.obj N) ≫ g.map (B.hom.app N) ≫ P.hom.app (a.obj N)) :
    u ≫ c.map (ψ ≫ s.map τ ≫ Q.hom.app N) = u ≫ c.map δ := by
  apply (cancel_mono (C.hom.app N)).mp
  simp only [Functor.map_comp, Category.assoc]
  have hA := A.hom.naturality τ
  dsimp only [Functor.comp_map] at hA
  rw [hcoh, reassoc_of% hA, reassoc_of% hE]
  have hBg := congrArg g.map hB
  simp only [Functor.map_comp] at hBg
  rw [reassoc_of% hBg]
  have hPN := P.hom.naturality z
  dsimp only [Functor.comp_map] at hPN
  rw [hPN, reassoc_of% hP, hD]

private theorem comp_four_inv_of_eq {C : Type*} [Category C]
    {T A B D E F G : C} (u : T ⟶ A) (v : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E)
    (e : F ≅ E) (w : T ⟶ G) (z : G ⟶ F)
    (h : u ≫ v ≫ a ≫ b = w ≫ z ≫ e.hom) :
    u ≫ v ≫ a ≫ b ≫ e.inv = w ≫ z := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the finite coefficient h-map composes the two restricted
pullback units. This is an identity of module-sheaf morphisms, before applying
cohomology, and uses no resolutions beyond the unit-square fields of E and D.
Source: Stacks Project, Tag 02OD, factorization through the local spectrum;
Tags 01F7 and 01FB, composition and restriction of h-maps.
(blueprint: lem-weil-pbc-formal-functions-finite-open-unit-pasting)

Proof: Let g be the local projection, j the finite map, and i the finite
projection; j followed by g equals i. Transpose the definition of
formalFunctionsFiniteFMap along tensorPullback g. Its transpose is the i-unit,
followed by the inverse pushforward-composition identification and the
projection-equality identification. Thus the g-unit followed by g_* of the
finite h-map is the i-unit with these identifications.
Transpose the desired equation under the restriction adjunction for U. Use
E.unit_square to replace the transpose of E.psi with the g-unit followed by
the restriction unit for U'. Naturality of pushforwardComp and pushforwardCongr
moves the pushed-forward restricted finite h-map past these identifications.
The assumed square hτ replaces the U'-restriction unit followed by τ by the
finite h-map followed by the W-restriction unit. The preceding global unit
identity then gives the i-unit followed by that restriction unit. D.unit_square
identifies this with the transpose of D.psi. The remaining composition
identifications agree: on an open subset of U, each is the identity followed by
the restriction map associated to the equality of the two inverse images.
Their equality follows from the presheaf composition law and proof irrelevance.
Cancel the invertible pushforward identifications and use injectivity of the
restriction adjunction homEquiv to obtain the displayed equation.
The argument also applies to empty opens and zero coefficients, when every
component is the zero map; it does not assume any open contains y. -/
theorem formalFunctions_finite_open_unit_pasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (F : X.Modules) (n : ℕ) (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (J : InjectiveResolution ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))
    (V : Y.Opens)
    (E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (formalFibreBaseMap Y y n) F I J V) :
    let g := pullback.snd (Y.fromSpecStalk y) f
    let j := formalFunctionsFiniteι f y n
    let i := formalFibreι f y n
    let U := f ⁻¹ᵁ V
    let U' := g ⁻¹ᵁ U
    let W := i ⁻¹ᵁ U
    let F' := (Scheme.Modules.tensorPullback g).obj F
    let Fₙ := (Scheme.Modules.tensorPullback i).obj F
    ∀ (hle : W ≤ j ⁻¹ᵁ U'),
      let r := j.resLE U' W hle
      let s := g.resLE U U' le_rfl
      let q := i.resLE U W le_rfl
      ∀ (hrs : r ≫ s = q)
        (τ : (Scheme.Modules.restrictFunctor U'.ι).obj F' ⟶
          (Scheme.Modules.pushforward r).obj ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ)),
        (Scheme.Modules.restrictAdjunction U'.ι).unit.app F' ≫
          (Scheme.Modules.pushforward U'.ι).map τ ≫
          (Scheme.Modules.pushforwardComp r U'.ι).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) ≫
          (Scheme.Modules.pushforwardCongr (j.resLE_comp_ι hle)).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) =
        formalFunctionsFiniteFMap f y F n ≫ (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictAdjunction W.ι).unit.app Fₙ) ≫
          (Scheme.Modules.pushforwardComp W.ι j).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) →
        E.psi ≫ (Scheme.Modules.pushforward s).map τ ≫
          (Scheme.Modules.pushforwardComp r s).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) ≫
          (Scheme.Modules.pushforwardCongr hrs).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) = D.psi := by
  intro g j i U U' W F' Fₙ hle r s q hrs τ hτ
  let N := (Scheme.Modules.restrictFunctor W.ι).obj Fₙ
  have hφ :
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app F ≫
        (Scheme.Modules.pushforward g).map (formalFunctionsFiniteFMap f y F n) =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app F ≫
        (Scheme.Modules.pushforwardCongr (formalFunctionsFiniteι_snd f y n).symm).hom.app
          Fₙ ≫ (Scheme.Modules.pushforwardComp j g).inv.app Fₙ := by
    exact ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv
      F _).apply_symm_apply _
  let M := (Scheme.Modules.restrictFunctor U'.ι).obj F'
  let A := Scheme.Modules.pushforwardComp s U.ι ≪≫
    Scheme.Modules.pushforwardCongr (g.resLE_comp_ι le_rfl) ≪≫
    (Scheme.Modules.pushforwardComp U'.ι g).symm
  let B := Scheme.Modules.pushforwardComp r U'.ι ≪≫
    Scheme.Modules.pushforwardCongr (j.resLE_comp_ι hle) ≪≫
    (Scheme.Modules.pushforwardComp W.ι j).symm
  let C := Scheme.Modules.pushforwardComp q U.ι ≪≫
    Scheme.Modules.pushforwardCongr (i.resLE_comp_ι le_rfl) ≪≫
    (Scheme.Modules.pushforwardComp W.ι i).symm
  let P := Scheme.Modules.pushforwardComp j g ≪≫
    Scheme.Modules.pushforwardCongr (formalFunctionsFiniteι_snd f y n)
  let Q := Scheme.Modules.pushforwardComp r s ≪≫
    Scheme.Modules.pushforwardCongr hrs
  have hE : (Scheme.Modules.restrictAdjunction U.ι).unit.app F ≫
      (Scheme.Modules.pushforward U.ι).map E.psi ≫ A.hom.app M =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app F ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.restrictAdjunction U'.ι).unit.app F') := by
    exact comp_four_inv_of_eq _ _ _ _ ((Scheme.Modules.pushforwardComp U'.ι g).app M)
      _ _ E.unit_square
  have hB : (Scheme.Modules.restrictAdjunction U'.ι).unit.app F' ≫
      (Scheme.Modules.pushforward U'.ι).map τ ≫ B.hom.app N =
      formalFunctionsFiniteFMap f y F n ≫ (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictAdjunction W.ι).unit.app Fₙ) := by
    exact comp_four_inv_of_eq _ _ _ _ ((Scheme.Modules.pushforwardComp W.ι j).app N)
      _ _ hτ
  have hD : (Scheme.Modules.restrictAdjunction U.ι).unit.app F ≫
      (Scheme.Modules.pushforward U.ι).map D.psi ≫ C.hom.app N =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app F ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.restrictAdjunction W.ι).unit.app Fₙ) := by
    exact comp_four_inv_of_eq _ _ _ _ ((Scheme.Modules.pushforwardComp W.ι i).app N)
      _ _ D.unit_square
  have hP :
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app F ≫
        (Scheme.Modules.pushforward g).map (formalFunctionsFiniteFMap f y F n) ≫
          P.hom.app Fₙ =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app F := by
    rw [← Category.assoc, hφ]
    simp only [P, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app_assoc]
    rw [pushforwardCongr_symm_comp]
    exact Category.comp_id _
  have hcoh : (Scheme.Modules.pushforward U.ι).map (Q.hom.app N) ≫ C.hom.app N =
      A.hom.app ((Scheme.Modules.pushforward r).obj N) ≫
        (Scheme.Modules.pushforward g).map (B.hom.app N) ≫
          P.hom.app ((Scheme.Modules.pushforward W.ι).obj N) := by
    exact pushforward_restriction_coherence j g i W.ι U'.ι U.ι r s q
      (formalFunctionsFiniteι_snd f y n) (j.resLE_comp_ι hle)
      (g.resLE_comp_ι le_rfl) (i.resLE_comp_ι le_rfl) hrs N
  change E.psi ≫ (Scheme.Modules.pushforward s).map τ ≫ Q.hom.app N = D.psi
  apply ((Scheme.Modules.restrictAdjunction U.ι).homEquiv F _).injective
  exact paste_units (Scheme.Modules.pushforward U.ι) (Scheme.Modules.pushforward U'.ι)
    (Scheme.Modules.pushforward W.ι) (Scheme.Modules.pushforward g)
    (Scheme.Modules.pushforward j) (Scheme.Modules.pushforward i)
    (Scheme.Modules.pushforward s) (Scheme.Modules.pushforward r)
    (Scheme.Modules.pushforward q) A B C P Q
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app F)
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app F)
    ((Scheme.Modules.restrictAdjunction U'.ι).unit.app F')
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app F)
    ((Scheme.Modules.restrictAdjunction W.ι).unit.app Fₙ)
    E.psi τ D.psi (formalFunctionsFiniteFMap f y F n) hE hB hD hP hcoh

end AlgebraicGeometry
