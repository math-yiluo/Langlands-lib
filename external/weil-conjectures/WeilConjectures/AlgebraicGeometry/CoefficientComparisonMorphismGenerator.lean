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

/-- (blueprint: lem-pc-coefficient-comparison-morphism-generator) -/
private theorem hom_restrict_apply {S : Scheme.{u}} {A D : S.Modules}
    (φ : A ⟶ D) {B C : S.Opens} (i : B ⟶ C) (s : Γ(A, C)) :
    φ.app B (A.presheaf.map i.op s) = D.presheaf.map i.op (φ.app C s) := by
  exact congrArg (fun k ↦ k s) (φ.mapPresheaf.naturality i.op)

/-- The concrete mate sends the three-unit generator to the pullback-unit section.
Source: Stacks Project, Tag 01I6, Lemma 26.7.1; Tags 0096 and 0097.
(blueprint: lem-pc-coefficient-comparison-morphism-generator).
Proof: Apply the hom equivalence of the composed tilde/Gamma and two pullback
adjunctions to the defining mate. Equiv.apply_symm_apply gives the original
linear section map. Expand the composed unit: its components are tilde.toOpen,
then the unit for U.toSpecGamma and the unit for g. Naturality of the second
unit moves the first full-open restriction past it; naturality of the mate
moves the last restriction past the mate. The two resulting restrictions on
the target, followed by the support identification, compose to restriction
from the inverse-image support to W intersect fprime inverse image top.
Expand the original linear section map and combine its restriction with this
one by functoriality. This is precisely the pullback-unit section restricted
through hW and then to the displayed intersection. Proof irrelevance identifies
all inclusion and equality morphisms. No affine or cartesian hypothesis is used. -/
theorem coefficientComparisonMorphism_generator {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι)) (W : X'.Opens)
    (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
      ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ s : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z),
      (M.presheaf.map (eqToHom (show
          W ⊓ f' ⁻¹ᵁ ⊤ = W.ι ''ᵁ ((W.ι ≫ f') ⁻¹ᵁ ⊤) by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι])).op)
        ((coefficientComparisonMorphism f F U Z g g' f' w W hW).app ⊤
          (let e := (tilde.toOpen N ⊤) s
           let e' := ((pullbackPushforwardAdjunction U.toScheme.toSpecΓ).unit.app
             (tilde N)).app ⊤ e
           let e'' := ((pullback U.toScheme.toSpecΓ).obj (tilde N)).presheaf.map
             (homOfLE (show ⊤ ≤ U.toScheme.toSpecΓ ⁻¹ᵁ ⊤ by simp)).op e'
           ((pullback g).obj ((pullback U.toScheme.toSpecΓ).obj (tilde N))).presheaf.map
             (homOfLE (show ⊤ ≤ g ⁻¹ᵁ ⊤ by simp)).op
               (((pullbackPushforwardAdjunction g).unit.app
                 ((pullback U.toScheme.toSpecΓ).obj (tilde N))).app ⊤ e''))) =
      M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ ⊤ ≤ W)).op
        (M.presheaf.map (homOfLE hW.le).op
          (((pullbackPushforwardAdjunction g').unit.app F).app ((f ⁻¹ᵁ U).ι ''ᵁ Z)
            ((F.restrictAppIso (f ⁻¹ᵁ U).ι Z).hom s))) := by
  dsimp only
  intro s
  let adj := ((tilde.adjunction (R := Γ(U.toScheme, ⊤))).comp
    (pullbackPushforwardAdjunction U.toScheme.toSpecΓ)).comp
      (pullbackPushforwardAdjunction g)
  have hm := (adj.homEquiv _ _).apply_symm_apply
    (coefficientSectionLinearMap f F U Z g g' f' w W hW)
  rw [Adjunction.homEquiv_unit] at hm
  have hs := congrArg (fun k ↦ k s) hm
  simp only [adj, Adjunction.comp_unit_app, Functor.comp_map, ModuleCat.comp_apply] at hs
  let N := (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
    ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
  let q := coefficientComparisonMorphism f F U Z g g' f' w W hW
  change q.app (g ⁻¹ᵁ (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤))
    (((pullbackPushforwardAdjunction g).unit.app
      ((pullback U.toScheme.toSpecΓ).obj (tilde N))).app (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤)
        (((pullbackPushforwardAdjunction U.toScheme.toSpecΓ).unit.app
          (tilde N)).app ⊤ ((tilde.toOpen N ⊤) s))) =
    coefficientSectionAddMap f F U Z g g' f' w W hW s at hs
  change _ = _
  -- Restrict the naturality rewrites to the section arguments of the outer maps.
  conv_lhs =>
    arg 2
    rw [hom_restrict_apply q]
    arg 2
    arg 2
    erw [hom_restrict_apply ((pullbackPushforwardAdjunction g).unit.app
      ((pullback U.toScheme.toSpecΓ).obj (tilde N)))]
  simp only [pushforward_obj_presheaf_map]
  conv_lhs =>
    arg 2
    arg 2
    erw [hom_restrict_apply q]
  rw [hs]
  dsimp only [coefficientSectionAddMap]
  let M := (pullback g').obj F
  let L₀ := W.ι ''ᵁ ((W.ι ≫ f') ⁻¹ᵁ ⊤)
  let L₁ := W.ι ''ᵁ ((W.ι ≫ f') ⁻¹ᵁ (g ⁻¹ᵁ ⊤))
  let L₂ := W.ι ''ᵁ ((W.ι ≫ f') ⁻¹ᵁ (g ⁻¹ᵁ (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤)))
  have h₀₁ : L₀ ≤ L₁ := by simp [L₀, L₁]
  have h₁₂ : L₁ ≤ L₂ := by simp [L₁, L₂]
  have h₂ : L₂ ≤ g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z) := by
    simpa [L₂, Scheme.Opens.opensRange_ι] using hW.le
  change M.presheaf.map (eqToHom (show W ⊓ f' ⁻¹ᵁ ⊤ = L₀ by
      simp [L₀, Scheme.Opens.opensRange_ι])).op
    (M.presheaf.map (homOfLE h₀₁).op (M.presheaf.map (homOfLE h₁₂).op
      (M.presheaf.map (homOfLE h₂).op
        (((pullbackPushforwardAdjunction g').unit.app F).app ((f ⁻¹ᵁ U).ι ''ᵁ Z)
          ((F.restrictAppIso (f ⁻¹ᵁ U).ι Z).hom s))))) = _
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
