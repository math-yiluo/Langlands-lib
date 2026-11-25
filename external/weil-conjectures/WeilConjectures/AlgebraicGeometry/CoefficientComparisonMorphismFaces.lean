/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstruction

/-! # Coefficient comparison by the composed adjunction

Source: Stacks Project, Tags 02KE, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def supportRestriction {S T : Scheme.{u}} (f : S ⟶ T) (M : S.Modules)
    {A D : S.Opens} (h : A ≤ D) :
    (pushforward (D.ι ≫ f)).obj (M.restrict D.ι) ⟶
      (pushforward (A.ι ≫ f)).obj (M.restrict A.ι) := by
  let i := S.homOfLE h
  let e : i ≫ (D.ι ≫ f) = A.ι ≫ f := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let er : (M.restrict D.ι).restrict i ≅ M.restrict A.ι :=
    (restrictFunctorComp i D.ι).symm.app M ≪≫
      (restrictFunctorCongr (S.homOfLE_ι h)).app M
  exact (pushforward (D.ι ≫ f)).map ((restrictAdjunction i).unit.app (M.restrict D.ι)) ≫
    (pushforwardComp i (D.ι ≫ f)).hom.app _ ≫
      (pushforwardCongr e).hom.app _ ≫ (pushforward (A.ι ≫ f)).map er.hom

-- The four dependent restriction and pushforward isomorphisms require extra reduction.
private theorem supportRestriction_app {S T : Scheme.{u}} (f : S ⟶ T) (M : S.Modules)
    {A D : S.Opens} (h : A ≤ D) (B : T.Opens)
    (s : Γ((pushforward (D.ι ≫ f)).obj (M.restrict D.ι), B)) :
    (M.restrictAppIso A.ι _).hom ((supportRestriction f M h).app B s) =
      M.presheaf.map (homOfLE (show
        A.ι ''ᵁ ((A.ι ≫ f) ⁻¹ᵁ B) ≤ D.ι ''ᵁ ((D.ι ≫ f) ⁻¹ᵁ B) by
          simp only [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
            Scheme.Opens.opensRange_ι]
          exact inf_le_inf h le_rfl)).op ((M.restrictAppIso D.ι _).hom s) := by
  simp only [supportRestriction, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app, pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    restrictAdjunction_unit_app_app, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app]
  simp only [restrict_map, restrictAppIso, Iso.refl_hom]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _
    (M.presheaf.map _ s))) = M.presheaf.map _ s
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  rfl


-- Comparing nested direct images requires reducing their scalar-restriction instances.
private theorem coefficientSectionLinearMap_naturality
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules) (U : T.Opens)
    {Z D : (f ⁻¹ᵁ U).toScheme.Opens} (h : Z ≤ D)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι)) {A E : X'.Opens} (hAE : A ≤ E)
    (hA : A = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (hE : E = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ D)) :
    (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).map
      ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.map (homOfLE h).op) ≫
        coefficientSectionLinearMap f F U Z g g' f' w A hA =
    coefficientSectionLinearMap f F U D g g' f' w E hE ≫
      (pushforward g ⋙ pushforward U.toScheme.toSpecΓ ⋙ moduleSpecΓFunctor).map
        (supportRestriction f' ((pullback g').obj F) hAE) := by
  ext s
  change Γ(F, (f ⁻¹ᵁ U).ι ''ᵁ D) at s
  change coefficientSectionAddMap f F U Z g g' f' w A hA
    ((F.restrict (f ⁻¹ᵁ U).ι).presheaf.map (homOfLE h).op s) =
      (supportRestriction f' ((pullback g').obj F) hAE).app
        (g ⁻¹ᵁ (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤))
          (coefficientSectionAddMap f F U D g g' f' w E hE s)
  have hs := supportRestriction_app f' ((pullback g').obj F) hAE
    (g ⁻¹ᵁ (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤))
      (coefficientSectionAddMap f F U D g g' f' w E hE s)
  change (supportRestriction f' ((pullback g').obj F) hAE).app
    (g ⁻¹ᵁ (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤))
      (coefficientSectionAddMap f F U D g g' f' w E hE s) = _ at hs
  refine Eq.trans ?_ hs.symm
  let η := (pullbackPushforwardAdjunction g').unit.app F
  let i := homOfLE (Scheme.Hom.image_mono (f ⁻¹ᵁ U).ι h)
  have hn := ConcreteCategory.congr_hom (η.mapPresheaf.naturality i.op) s
  change η.app ((f ⁻¹ᵁ U).ι ''ᵁ Z) (F.presheaf.map i.op s) =
    ((pullback g').obj F).presheaf.map _ (η.app ((f ⁻¹ᵁ U).ι ''ᵁ D) s) at hn
  change ((pullback g').obj F).presheaf.map _
    (η.app ((f ⁻¹ᵁ U).ι ''ᵁ Z) (F.presheaf.map i.op s)) =
      ((pullback g').obj F).presheaf.map _
        (((pullback g').obj F).presheaf.map _
          (η.app ((f ⁻¹ᵁ U).ι ''ᵁ D) s))
  rw [hn]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The composed adjunction compares dependent scalar-restriction and direct-image instances.
/-- The concrete coefficient mates commute with every Cech face restriction.
Source: Stacks Project, Tags 02KE and 0097, naturality of the termwise map.
(blueprint: lem-pc-coefficient-comparison-morphism-faces).
Proof: Restriction of sections from an intersection with a deleted index to the
full intersection commutes with restrictAppIso and with the pullback unit.
Thus the explicitly defined section maps commute with the source restriction
and the support restriction on the target. Take mates under the composed
adjunction. Naturality of the hom equivalence on both sides gives equality of
module morphisms after the coefficient restriction. Evaluate on B and use
naturality of the support identifications. Their equality morphisms and the
inclusions of supports compose to the single inclusion displayed here, by
proof irrelevance in the poset of opens. For empty opens the same identities
hold; for an empty tuple family there is no face to check. -/
theorem coefficientComparisonMorphism_faces {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι))
    (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t =
        g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ alternatingCechIntersection V t)) :
    let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
    let H := ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
      tilde.functor Γ(U.toScheme, ⊤) ⋙
      Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
    let M := (Modules.pullback g').obj F
    let W := fun (p : ℕ) (t : Fin (p + 1) ↪o Fin r) ↦
      alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t
    ∀ (p : ℕ) (t : Fin (p + 2) ↪o Fin r) (j : Fin (p + 2)) (B : T'.Opens)
        (s : Γ(H.obj (G.obj (op (alternatingCechIntersection V
          ((Fin.succAboveOrderEmb j).trans t)))), B)),
        (M.presheaf.map (eqToHom (show
          (W (p + 1) t) ⊓ f' ⁻¹ᵁ B = (W (p + 1) t).ι ''ᵁ (((W (p + 1) t).ι ≫ f') ⁻¹ᵁ B) by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι])).op)
          ((coefficientComparisonMorphism f F U (alternatingCechIntersection V t)
              g g' f' w (W (p + 1) t)
              (hW (p + 1) t)).app B
            ((H.map (G.map (homOfLE
              (alternatingCechIntersection_face_le V p t j)).op)).app B s)) =
        M.presheaf.map (homOfLE (inf_le_inf
          (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
            ((M.presheaf.map (eqToHom (show
          (W p ((Fin.succAboveOrderEmb j).trans t)) ⊓ f' ⁻¹ᵁ B =
            (W p ((Fin.succAboveOrderEmb j).trans t)).ι ''ᵁ
              (((W p ((Fin.succAboveOrderEmb j).trans t)).ι ≫ f') ⁻¹ᵁ B) by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι])).op)
              ((coefficientComparisonMorphism f F U
                  (alternatingCechIntersection V ((Fin.succAboveOrderEmb j).trans t))
                  g g' f' w (W p ((Fin.succAboveOrderEmb j).trans t))
                  (hW p
                    ((Fin.succAboveOrderEmb j).trans t))).app B s)) := by
  intro G H M W p t j B s
  let Z := alternatingCechIntersection V t
  let D := alternatingCechIntersection V ((Fin.succAboveOrderEmb j).trans t)
  let A := alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t
  let E := alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩)
    ((Fin.succAboveOrderEmb j).trans t)
  have hZD : Z ≤ D := alternatingCechIntersection_face_le V p t j
  have hAE : A ≤ E := alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j
  let K := ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)
  let adj := ((tilde.adjunction (R := Γ(U.toScheme, ⊤))).comp
    (pullbackPushforwardAdjunction U.toScheme.toSpecΓ)).comp
      (pullbackPushforwardAdjunction g)
  have hn := adj.homEquiv_naturality_right_square
        (X' := K.obj (G.obj (op D))) (X := K.obj (G.obj (op Z)))
        (Y := (pushforward (E.ι ≫ f')).obj (M.restrict E.ι))
        (Y' := (pushforward (A.ι ≫ f')).obj (M.restrict A.ι))
        (K.map (G.map (homOfLE hZD).op))
        (coefficientSectionLinearMap f F U Z g g' f' w A (hW (p + 1) t))
        (coefficientSectionLinearMap f F U D g g' f' w E
          (hW p ((Fin.succAboveOrderEmb j).trans t)))
        (supportRestriction f' M (A := A) (D := E) hAE)
        (coefficientSectionLinearMap_naturality f F U (Z := Z) (D := D)
          hZD g g' f' w (A := A) (E := E) hAE
          (hW (p + 1) t) (hW p ((Fin.succAboveOrderEmb j).trans t)))
  have hm : H.map (G.map (homOfLE hZD).op) ≫
      coefficientComparisonMorphism f F U Z g g' f' w A (hW (p + 1) t) =
    coefficientComparisonMorphism f F U D g g' f' w E
        (hW p ((Fin.succAboveOrderEmb j).trans t)) ≫
      supportRestriction f' M (A := A) (D := E) hAE := by
    unfold coefficientComparisonMorphism
    exact hn
  have ha := congrArg
    (fun k : H.obj (G.obj (op D)) ⟶
      (pushforward (A.ι ≫ f')).obj (M.restrict A.ι) ↦ k.app B s) hm
  change (coefficientComparisonMorphism f F U Z g g' f' w A
      (hW (p + 1) t)).app B ((H.map (G.map (homOfLE hZD).op)).app B s) =
    (supportRestriction f' M (A := A) (D := E) hAE).app B
      ((coefficientComparisonMorphism f F U D g g' f' w E
        (hW p ((Fin.succAboveOrderEmb j).trans t))).app B s) at ha
  let eA : A ⊓ f' ⁻¹ᵁ B = A.ι ''ᵁ ((A.ι ≫ f') ⁻¹ᵁ B) := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
  refine Eq.trans (congrArg (fun x ↦ M.presheaf.map (eqToHom eA).op x) ha) ?_
  let v := (coefficientComparisonMorphism f F U D g g' f' w E
    (hW p ((Fin.succAboveOrderEmb j).trans t))).app B s
  have hs := supportRestriction_app f' M (A := A) (D := E) hAE B v
  change (supportRestriction f' M (A := A) (D := E) hAE).app B v = _ at hs
  refine Eq.trans (congrArg (fun x ↦ M.presheaf.map (eqToHom eA).op x) hs) ?_
  let eE : E ⊓ f' ⁻¹ᵁ B = E.ι ''ᵁ ((E.ι ≫ f') ⁻¹ᵁ B) := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
  have hi : A.ι ''ᵁ ((A.ι ≫ f') ⁻¹ᵁ B) ≤ E.ι ''ᵁ ((E.ι ≫ f') ⁻¹ᵁ B) := by
    simp only [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    exact inf_le_inf hAE le_rfl
  let i := (homOfLE hi).op
  let a := (eqToHom eA).op
  let d := (eqToHom eE).op
  let b : op (E ⊓ f' ⁻¹ᵁ B) ⟶ op (A ⊓ f' ⁻¹ᵁ B) :=
    (homOfLE (inf_le_inf hAE le_rfl)).op
  have hc : i ≫ a = d ≫ b := Subsingleton.elim _ _
  have he : M.presheaf.map i ≫ M.presheaf.map a =
      M.presheaf.map d ≫ M.presheaf.map b :=
    (M.presheaf.map_comp i a).symm.trans
      ((congrArg (fun k : op (E.ι ''ᵁ ((E.ι ≫ f') ⁻¹ᵁ B)) ⟶
        op (A ⊓ f' ⁻¹ᵁ B) ↦ M.presheaf.map k) hc).trans
          (M.presheaf.map_comp d b))
  change Γ(M, E.ι ''ᵁ ((E.ι ≫ f') ⁻¹ᵁ B)) at v
  change (M.presheaf.map i ≫ M.presheaf.map a) v =
    (M.presheaf.map d ≫ M.presheaf.map b) v
  exact ConcreteCategory.congr_hom he v

end
end AlgebraicGeometry.Scheme.Modules
