import Langlands.AlgebraicGeometry.RelativeDifferentialsOpenImmersionStatement

/-! # Open-immersion locality of relative differentials: proof -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules Opposite

namespace Langlands.Scheme

namespace RelativeDerivation

section OpenImmersion

variable {X' X S : AlgebraicGeometry.Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g]
  {f : X ⟶ S} {M : X'.Modules}

/-- The components of the derivation on `X'` induced by a derivation into the
pushforward along an open immersion `g`. -/
def openImmersionLiftApp (D : RelativeDerivation f ((pushforward g).obj M))
    (V : X'.Opens) : Γ(X', V) →+ Γ(M, V) :=
  (M.presheaf.map (homOfLE (g.preimage_image_eq V).ge).op).hom.comp
    ((D.app (g ''ᵁ V)).comp (g.appIso V).inv.hom.toAddMonoidHom)

lemma openImmersionLiftApp_apply (D : RelativeDerivation f ((pushforward g).obj M))
    (V : X'.Opens) (a : Γ(X', V)) :
    openImmersionLiftApp g D V a =
      M.presheaf.map (homOfLE (g.preimage_image_eq V).ge).op
        (D.app (g ''ᵁ V) ((g.appIso V).inv a)) := rfl

lemma map_app_appIso_inv (V : X'.Opens) (a : Γ(X', V)) :
    X'.presheaf.map (homOfLE (g.preimage_image_eq V).ge).op
      (g.app (g ''ᵁ V) ((g.appIso V).inv a)) = a :=
  ConcreteCategory.congr_hom (g.appIso_inv_app_presheafMap V) a

/-- Two successive restrictions of a section agree with any direct restriction. -/
lemma map_map_eq {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules) {U V W : Y.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (x : Γ(N, U)) :
    N.presheaf.map j.op (N.presheaf.map i.op x) = N.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- On sections pulled back along `g`, the induced derivation is the given one. -/
lemma openImmersionLiftApp_app (D : RelativeDerivation f ((pushforward g).obj M))
    (U : X.Opens) (a : Γ(X, U)) :
    openImmersionLiftApp g D (g ⁻¹ᵁ U) (g.app U a) = D.app U a := by
  have h₁ : (g.appIso (g ⁻¹ᵁ U)).inv (g.app U a) =
      X.presheaf.map (homOfLE (Set.image_preimage_subset g U.1) : g ''ᵁ (g ⁻¹ᵁ U) ⟶ U).op a := by
    rw [← ConcreteCategory.comp_apply, g.app_appIso_inv]
    rfl
  rw [openImmersionLiftApp_apply, h₁, app_restrict, pushforward_obj_presheaf_map]
  exact (map_map_eq M _ _ (𝟙 _) _).trans (ConcreteCategory.congr_hom (M.presheaf.map_id _) _)

lemma openImmersionLiftApp_restrict (D : RelativeDerivation f ((pushforward g).obj M))
    {V W : X'.Opens} (i : V ⟶ W) (a : Γ(X', W)) :
    openImmersionLiftApp g D V (X'.presheaf.map i.op a) =
      M.presheaf.map i.op (openImmersionLiftApp g D W a) := by
  simp only [openImmersionLiftApp_apply]
  rw [← ConcreteCategory.comp_apply (X'.presheaf.map i.op), g.appIso_inv_naturality,
    ConcreteCategory.comp_apply]
  change M.presheaf.map _ (D.app _ (X.presheaf.map (g.opensFunctor.map i).op _)) = _
  rw [app_restrict, pushforward_obj_presheaf_map]
  exact (map_map_eq M _ _ (i ≫ homOfLE (g.preimage_image_eq W).ge) _).trans
    (map_map_eq M _ _ _ _).symm

lemma openImmersionLiftApp_mul (D : RelativeDerivation f ((pushforward g).obj M))
    (V : X'.Opens) (a c : Γ(X', V)) :
    openImmersionLiftApp g D V (a * c) =
      a • openImmersionLiftApp g D V c + c • openImmersionLiftApp g D V a := by
  simp only [openImmersionLiftApp_apply, map_mul, app_mul]
  change M.presheaf.map _ (g.app (g ''ᵁ V) ((g.appIso V).inv a) • _ +
    g.app (g ''ᵁ V) ((g.appIso V).inv c) • _) = _
  rw [map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_app_appIso_inv,
    map_app_appIso_inv]

variable {S' : AlgebraicGeometry.Scheme.{u}} (b : S' ⟶ S) [IsOpenImmersion b]
  {f' : X' ⟶ S'} (w : g ≫ f = f' ≫ b)

include w in
lemma openImmersionLiftApp_base (D : RelativeDerivation f ((pushforward g).obj M))
    (W : S'.Opens) (c : Γ(S', W)) :
    openImmersionLiftApp g D (f' ⁻¹ᵁ W) (f'.app W c) = 0 := by
  have hle : f' ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ (b ''ᵁ W)) := by
    intro x hx
    change f (g x) ∈ b ''ᵁ W
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    exact ⟨_, hx, rfl⟩
  have hc : c = b.appLE (b ''ᵁ W) W (b.preimage_image_eq W).ge ((b.appIso W).inv c) := by
    rw [← Scheme.Hom.appIso_hom', Iso.inv_hom_id_apply]
  have hcongr : ∀ (φ ψ : X' ⟶ S) (_ : φ = ψ) (U : S.Opens) (V : X'.Opens)
      (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U), φ.appLE U V e = ψ.appLE U V e' := by
    intro φ ψ h U V e e'
    subst h
    rfl
  have hkey : b.appLE (b ''ᵁ W) W (b.preimage_image_eq W).ge ≫ f'.app W =
      f.app (b ''ᵁ W) ≫ g.appLE (f ⁻¹ᵁ (b ''ᵁ W)) (f' ⁻¹ᵁ W) hle := by
    rw [f'.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    exact hcongr _ _ w.symm _ _ _ _
  have key : f'.app W c =
      g.appLE (f ⁻¹ᵁ (b ''ᵁ W)) (f' ⁻¹ᵁ W) hle (f.app (b ''ᵁ W) ((b.appIso W).inv c)) := by
    conv_lhs => rw [hc]
    exact ConcreteCategory.congr_hom hkey _
  rw [key, Scheme.Hom.appLE, ConcreteCategory.comp_apply, openImmersionLiftApp_restrict,
    openImmersionLiftApp_app, app_base, map_zero]

/-- The relative derivation on `X'` over `S'` induced by a derivation into the
pushforward along `g`, for a commutative square of open immersions. -/
def openImmersionLift (D : RelativeDerivation f ((pushforward g).obj M)) :
    RelativeDerivation f' M where
  d {V} := openImmersionLiftApp g D V.unop
  d_mul {V} a c := openImmersionLiftApp_mul g D V.unop a c
  d_map i a := openImmersionLiftApp_restrict g D i.unop a
  d_app {W} c := openImmersionLiftApp_base g b w D W.unop c

@[simp]
lemma openImmersionLift_app (D : RelativeDerivation f ((pushforward g).obj M))
    (V : X'.Opens) (a : Γ(X', V)) :
    (openImmersionLift g b w D).app V a = openImmersionLiftApp g D V a := rfl

lemma precompOver_forgetBase_openImmersionLift
    (D : RelativeDerivation f ((pushforward g).obj M)) :
    precompOver g w (forgetBase b (openImmersionLift g b w D)) = D := by
  ext U a
  change (precompOver g w (forgetBase b (openImmersionLift g b w D))).app U.unop a =
    D.app U.unop a
  rw [precompOver_app, forgetBase_app, openImmersionLift_app, openImmersionLiftApp_app]

lemma openImmersionLift_precompOver_forgetBase (d : RelativeDerivation f' M) :
    openImmersionLift g b w (precompOver g w (forgetBase b d)) = d := by
  ext V a
  change (openImmersionLift g b w (precompOver g w (forgetBase b d))).app V.unop a =
    d.app V.unop a
  rw [openImmersionLift_app, openImmersionLiftApp_apply, precompOver_app, forgetBase_app,
    ← app_restrict, map_app_appIso_inv]

lemma bijective_precompOver_forgetBase :
    Function.Bijective (fun d : RelativeDerivation f' M =>
      precompOver g w (forgetBase b d)) :=
  ⟨Function.LeftInverse.injective (g := openImmersionLift g b w)
      (openImmersionLift_precompOver_forgetBase g b w),
    Function.RightInverse.surjective (g := openImmersionLift g b w)
      (precompOver_forgetBase_openImmersionLift g b w)⟩

end OpenImmersion

end RelativeDerivation

/-- The canonical relative-differential map of a commutative square of open
immersions is an isomorphism. -/
theorem relativeDifferentialsOpenImmersionIsIso :
    RelativeDifferentialsOpenImmersionIsIsoStatement.{u} := by
  intro X' X S' S f f' g b _ _ w
  apply isIso_of_coyoneda_map_bijective
  intro M
  let e₁ := relativeDifferentialsHomEquiv f' M
  let e₂ := ((pullbackPushforwardAdjunction g).homEquiv _ _).trans
    (relativeDifferentialsHomEquiv f ((pushforward g).obj M))
  have hcomm : (fun α => relativeDifferentialsSquareMap g b w ≫ α) =
      e₂.symm ∘ (fun d => RelativeDerivation.precompOver g w
        (RelativeDerivation.forgetBase b d)) ∘ e₁ := by
    funext α
    apply e₂.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, e₁, e₂, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_right,
      relativeDifferentialsSquareMap_adjoint, relativeDifferentialsHomEquiv_apply,
      RelativeDerivation.postcomp_comp, relativeDifferentialsSquarePushforwardMap_fac,
      RelativeDerivation.forgetBase_postcomp,
      RelativeDerivation.precompOver_postcomp]
  rw [hcomm]
  exact e₂.symm.bijective.comp
    ((RelativeDerivation.bijective_precompOver_forgetBase g b w).comp e₁.bijective)

end Langlands.Scheme
