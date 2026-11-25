/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.CategoryTheory.Sites.TorsorGluing

/-!
# Additivity of `L ↦ Isom(𝒪, L)`

The torsor `Isom(𝒪, L)` is trivialised over the Zariski opens where `L` has a generator, with
transition functions those of the generators. Since the transition functions of `e ⊗ e'` are the
products of those of `e` and `e'`, the class of `Isom(𝒪, L ⊗ L')` in `H¹(X_ét, 𝔾ₘ)` is the sum of
the classes of `Isom(𝒪, L)` and `Isom(𝒪, L')`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.etaleIsoTorsor_sub_eq`: the difference of the trivialisations
  attached to generators `e₁` and `e₂ = c • e₁` is the pullback of `c`.
- `AlgebraicGeometry.Scheme.Modules.classH1_etaleIsoTorsor_tensorObj`: additivity.
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (A : modulesPseudofunctor.obj (.mk (op X)))
  [SheafOfModules.IsInvertible.{u, u, u} (A : X.Modules)]

private lemma etaleIsoTorsorVal_map_mk {V Z : X.Etale} (a : Z ⟶ V)
    (φ : (modulesPseudofunctor.map V.hom.op.toLoc).toFunctor.obj (unitObj X) ⟶
      (modulesPseudofunctor.map V.hom.op.toLoc).toFunctor.obj A) (hφ : IsIso φ) :
    etaleIsoTorsorVal A ((etaleIsoTorsor A).sheaf.obj.map a.op (etaleIsoTorsorMk A φ hφ)) =
      pullHom (F := modulesPseudofunctor) (M₁ := unitObj X) (M₂ := A)
        (f₁ := V.hom) (f₂ := V.hom) φ a.left Z.hom Z.hom
        (MorphismProperty.Over.w a) (MorphismProperty.Over.w a) := by
  change (modulesPseudofunctor.presheafHom (unitObj X) A).map
    ((toProEt X ⋙ ProEt.forget X).map a).op φ = _
  simp only [Pseudofunctor.presheafHom_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]
  rfl

omit [SheafOfModules.IsInvertible.{u, u, u} (A : X.Modules)] in
private lemma homSection_eq_scalar_of_generators {Y : Scheme.{u}} (f : Y ⟶ X)
    {U₁ U₂ : X.Opens} (e₁ : Γ((A : X.Modules), U₁)) (e₂ : Γ((A : X.Modules), U₂))
    (he₁ : IsFreeGenerator e₁) (c : Γ(X, U₁ ⊓ U₂))
    (h : (A : X.Modules).presheaf.map (homOfLE inf_le_right).op e₂ =
      c • (A : X.Modules).presheaf.map (homOfLE inf_le_left).op e₁)
    (h₁ : f ⁻¹ᵁ U₁ = ⊤) (h₂ : f ⁻¹ᵁ U₂ = ⊤)
    (ψ₁ ψ₂ : (pullback f).obj (unit X) ⟶ (pullback f).obj (A : X.Modules))
    (hs₁ : homSection f ψ₁ = genSection f e₁ h₁)
    (hs₂ : homSection f ψ₂ = genSection f e₂ h₂)
    (d : Γ(Y, ⊤)) (hd : smulHom ((pullback f).obj (unit X)) d ≫ ψ₁ = ψ₂) :
    d = f.appLE (U₁ ⊓ U₂) ⊤ (preimage_inf_eq_top f h₁ h₂).ge c := by
  have k := congrArg (homSection f (A := (A : X.Modules))) hd
  rw [homSection_smulHom_comp, hs₁, hs₂, genSection_eq_smul f e₁ e₂ c h h₁ h₂] at k
  have hg : IsFreeGenerator (genSection f e₁ h₁) := (he₁.pullback_unit_app f).map _
  exact (Scheme.presheaf_map_id_apply (X := Y) _ _).symm.trans (hg.smul_left_injective k)

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
/-- The difference of two trivialisations of `Isom(𝒪, A)` attached to generators `e₁`, `e₂` with
`e₂ = c • e₁` is the pullback of `c`. -/
lemma etaleIsoTorsor_sub_eq {V₁ V₂ Z : X.Etale} (a : Z ⟶ V₁) (b : Z ⟶ V₂) {U₁ U₂ : X.Opens}
    (e₁ : Γ((A : X.Modules), U₁)) (e₂ : Γ((A : X.Modules), U₂)) (he₁ : IsFreeGenerator e₁)
    (c : Γ(X, U₁ ⊓ U₂))
    (h : (A : X.Modules).presheaf.map (homOfLE inf_le_right).op e₂ =
      c • (A : X.Modules).presheaf.map (homOfLE inf_le_left).op e₁)
    (hU₁ : V₁.hom ⁻¹ᵁ U₁ = ⊤) (hU₂ : V₂.hom ⁻¹ᵁ U₂ = ⊤) (hZ₁ : Z.hom ⁻¹ᵁ U₁ = ⊤)
    (hZ₂ : Z.hom ⁻¹ᵁ U₂ = ⊤)
    (φ₁ : (modulesPseudofunctor.map V₁.hom.op.toLoc).toFunctor.obj (unitObj X) ⟶
      (modulesPseudofunctor.map V₁.hom.op.toLoc).toFunctor.obj A) (hφ₁ : IsIso φ₁)
    (hs₁ : homSection V₁.hom φ₁ = genSection V₁.hom e₁ hU₁)
    (φ₂ : (modulesPseudofunctor.map V₂.hom.op.toLoc).toFunctor.obj (unitObj X) ⟶
      (modulesPseudofunctor.map V₂.hom.op.toLoc).toFunctor.obj A) (hφ₂ : IsIso φ₂)
    (hs₂ : homSection V₂.hom φ₂ = genSection V₂.hom e₂ hU₂) :
    ((Additive.toMul ((etaleIsoTorsor A).sub
        ((etaleIsoTorsor A).sheaf.obj.map a.op (etaleIsoTorsorMk A φ₁ hφ₁))
        ((etaleIsoTorsor A).sheaf.obj.map b.op (etaleIsoTorsorMk A φ₂ hφ₂))).down :
          Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) =
      Z.hom.appLE (U₁ ⊓ U₂) ⊤ (preimage_inf_eq_top Z.hom hZ₁ hZ₂).ge c := by
  set x₁ := (etaleIsoTorsor A).sheaf.obj.map a.op (etaleIsoTorsorMk A φ₁ hφ₁)
  set x₂ := (etaleIsoTorsor A).sheaf.obj.map b.op (etaleIsoTorsorMk A φ₂ hφ₂)
  have hv := congrArg (etaleIsoTorsorVal A) ((etaleIsoTorsor A).sub_vadd x₁ x₂)
  rw [etaleIsoTorsorVal_vadd] at hv
  simp only [x₁, x₂, etaleIsoTorsorVal_map_mk] at hv
  exact homSection_eq_scalar_of_generators A Z.hom e₁ e₂ he₁ c h hZ₁ hZ₂ _ _
    (homSection_pullHom V₁.hom a.left Z.hom _ e₁ hU₁ hZ₁ φ₁ hs₁)
    (homSection_pullHom V₂.hom b.left Z.hom _ e₂ hU₂ hZ₂ φ₂ hs₂) _ hv

lemma tmulSection_transition {M N : X.Modules} {U₁ U₂ : X.Opens} (s₁ : Γ(M, U₁)) (s₂ : Γ(M, U₂))
    (t₁ : Γ(N, U₁)) (t₂ : Γ(N, U₂)) (c d : Γ(X, U₁ ⊓ U₂))
    (hs : M.presheaf.map (homOfLE inf_le_right).op s₂ =
      c • M.presheaf.map (homOfLE inf_le_left).op s₁)
    (ht : N.presheaf.map (homOfLE inf_le_right).op t₂ =
      d • N.presheaf.map (homOfLE inf_le_left).op t₁) :
    (M ⊗ N).presheaf.map (homOfLE inf_le_right).op (tmulSection s₂ t₂) =
      (c * d) • (M ⊗ N).presheaf.map (homOfLE inf_le_left).op (tmulSection s₁ t₁) := by
  rw [tmulSection_map, tmulSection_map, hs, ht, smul_tmulSection, tmulSection_smul, mul_smul]

lemma exists_transition {M : X.Modules} {U₁ U₂ : X.Opens} {s₁ : Γ(M, U₁)}
    (hs₁ : IsFreeGenerator s₁) (s₂ : Γ(M, U₂)) :
    ∃ c : Γ(X, U₁ ⊓ U₂), M.presheaf.map (homOfLE inf_le_right).op s₂ =
      c • M.presheaf.map (homOfLE inf_le_left).op s₁ := by
  obtain ⟨c, hc⟩ := (hs₁.map (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).exists_smul_eq
    (M.presheaf.map (homOfLE inf_le_right).op s₂)
  exact ⟨c, hc.symm⟩

lemma preimage_eq_top_of_hom {V Z : X.Etale} (a : Z ⟶ V) {U : X.Opens}
    (hU : V.hom ⁻¹ᵁ U = ⊤) : Z.hom ⁻¹ᵁ U = ⊤ := by
  rw [← MorphismProperty.Over.w a]
  change a.left ⁻¹ᵁ (V.hom ⁻¹ᵁ U) = ⊤
  rw [hU]
  rfl

lemma gmSheaf_eq_add {Z : X.Etale} (a b c : X.gmSheaf.obj.obj (op Z))
    (h : ((Additive.toMul c.down : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) =
      ((Additive.toMul a.down : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) *
        ((Additive.toMul b.down : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤))) :
    c = a + b :=
  ULift.ext (Additive.toMul.injective (Units.ext (h.trans (Units.val_mul _ _).symm)))

-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
/-- **`L ↦ [Isom(𝒪, L)]` is additive.** The class of the `𝔾ₘ`-torsor `Isom(𝒪, L₁ ⊗ L₂)` is the sum
of the classes of `Isom(𝒪, L₁)` and `Isom(𝒪, L₂)`: on the Zariski opens where `L₁` and `L₂` have
generators `e₁`, `e₂`, the three torsors are trivialised by `e₁`, `e₂` and `e₁ ⊗ e₂`, whose
transition functions multiply. -/
theorem classH1_etaleIsoTorsor_tensorObj (L₁ L₂ : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L₁] [SheafOfModules.IsInvertible.{u, u, u} L₂]
    [SheafOfModules.IsInvertible.{u, u, u}
      (MonoidalCategoryStruct.tensorObj (C := X.Modules) L₁ L₂)]
    (hT : Limits.IsTerminal (Etale.mk (𝟙 X))) :
    Sheaf.Torsor.classH1 X.gmSheaf hT
        ⟦etaleIsoTorsor (MonoidalCategoryStruct.tensorObj (C := X.Modules) L₁ L₂)⟧ =
      Sheaf.Torsor.classH1 X.gmSheaf hT ⟦etaleIsoTorsor L₁⟧ +
        Sheaf.Torsor.classH1 X.gmSheaf hT ⟦etaleIsoTorsor L₂⟧ := by
  have hgen (x : X) : ∃ U : X.Opens, x ∈ U ∧ ∃ (e₁ : Γ(L₁, U))
      (e₂ : Γ(L₂, U)), IsFreeGenerator e₁ ∧ IsFreeGenerator e₂ := by
    obtain ⟨U₁, hx₁, -, f₁, hf₁⟩ := exists_isFreeGenerator L₁ (W := ⊤) (x := x)
      trivial
    obtain ⟨U₂, hx₂, hle, f₂, hf₂⟩ := exists_isFreeGenerator L₂ (W := U₁.1) hx₁
    exact ⟨U₂.1, hx₂, _, f₂, hf₁.map hle, hf₂⟩
  choose U hxU e₁ e₂ he₁ he₂ using hgen
  let R : Sieve (Etale.mk (𝟙 X)) :=
    { arrows V _ := ∃ x, V.hom ⁻¹ᵁ U x = ⊤
      downward_closed := fun {_ _ _} ⟨x, hx⟩ g ↦ ⟨x, preimage_eq_top_of_hom g hx⟩ }
  have hR : R ∈ X.smallEtaleTopology _ := by
    let W (x : X) : X.Etale := Etale.mk (U x).ι
    let ι (x : X) : W x ⟶ Etale.mk (𝟙 X) :=
      MorphismProperty.Over.homMk (U x).ι (Category.comp_id _)
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨x⟩
      exact ⟨x, Scheme.Opens.ι_preimage_self _⟩
    · refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, ⟨⟨y, hxU y⟩, ?_⟩⟩
      exact Scheme.Opens.ι_apply _ _
  have hφ (M : X.Modules) (e : ∀ x, Γ(M, U x)) (he : ∀ x, IsFreeGenerator (e x))
      (V : X.Etale) (hV : R (hT.from V)) :=
    exists_isIso_homSection_eq V.hom (he hV.choose) hV.choose_spec
  let t (M : modulesPseudofunctor.obj (.mk (op X))) [SheafOfModules.IsInvertible.{u, u, u}
      (M : X.Modules)] (e : ∀ x, Γ((M : X.Modules), U x)) (he : ∀ x, IsFreeGenerator (e x))
      (V : X.Etale) (hV : R (hT.from V)) : (etaleIsoTorsor M).sheaf.obj.obj (op V) :=
    etaleIsoTorsorMk M (hφ M e he V hV).choose (hφ M e he V hV).choose_spec.1
  have key (M : modulesPseudofunctor.obj (.mk (op X)))
      [SheafOfModules.IsInvertible.{u, u, u} (M : X.Modules)] (e : ∀ x, Γ((M : X.Modules), U x))
      (he : ∀ x, IsFreeGenerator (e x)) {V₁ V₂ Z : X.Etale} (h₁ : R (hT.from V₁))
      (h₂ : R (hT.from V₂)) (a : Z ⟶ V₁) (b : Z ⟶ V₂) (c : Γ(X, U h₁.choose ⊓ U h₂.choose))
      (hc : (M : X.Modules).presheaf.map (homOfLE inf_le_right).op (e h₂.choose) =
        c • (M : X.Modules).presheaf.map (homOfLE inf_le_left).op (e h₁.choose)) :
      ((Additive.toMul ((etaleIsoTorsor M).sub
        ((etaleIsoTorsor M).sheaf.obj.map a.op (t M e he V₁ h₁))
        ((etaleIsoTorsor M).sheaf.obj.map b.op (t M e he V₂ h₂))).down :
          Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) =
      Z.hom.appLE _ ⊤ (preimage_inf_eq_top Z.hom (preimage_eq_top_of_hom a h₁.choose_spec)
        (preimage_eq_top_of_hom b h₂.choose_spec)).ge c :=
    etaleIsoTorsor_sub_eq M a b (e h₁.choose) (e h₂.choose) (he _) c hc h₁.choose_spec
      h₂.choose_spec (preimage_eq_top_of_hom a h₁.choose_spec)
      (preimage_eq_top_of_hom b h₂.choose_spec) _ _ (hφ M e he V₁ h₁).choose_spec.2 _ _
      (hφ M e he V₂ h₂).choose_spec.2
  obtain ⟨μ, hμ, hμ₁, hμ₂⟩ := Sheaf.Torsor.exists_equivariant_of_sub_eq_add hT
    (etaleIsoTorsor L₁) (etaleIsoTorsor L₂)
    (etaleIsoTorsor (MonoidalCategoryStruct.tensorObj (C := X.Modules) L₁ L₂)) R hR
    (t L₁ e₁ he₁) (t L₂ e₂ he₂)
    (t _ (fun x ↦ tmulSection (e₁ x) (e₂ x)) (fun x ↦ (he₁ x).tmulSection (he₂ x))) (by
      intro V₁ V₂ Z h₁ h₂ a b
      obtain ⟨c₁, hc₁⟩ := exists_transition (he₁ h₁.choose) (e₁ h₂.choose)
      obtain ⟨c₂, hc₂⟩ := exists_transition (he₂ h₁.choose) (e₂ h₂.choose)
      have hc₃ := tmulSection_transition (e₁ h₁.choose) (e₁ h₂.choose) (e₂ h₁.choose)
        (e₂ h₂.choose) c₁ c₂ hc₁ hc₂
      refine gmSheaf_eq_add _ _ _ ?_
      rw [key (MonoidalCategoryStruct.tensorObj (C := X.Modules) L₁ L₂)
          (fun x ↦ tmulSection (e₁ x) (e₂ x)) (fun x ↦ (he₁ x).tmulSection (he₂ x)) h₁ h₂ a b _
          hc₃,
        key L₁ e₁ he₁ h₁ h₂ a b _ hc₁, key L₂ e₂ he₂ h₁ h₂ a b _ hc₂, map_mul])
  exact Sheaf.Torsor.classH1_eq_add_of_equivariant hT _ _ _ μ hμ hμ₁ hμ₂

end AlgebraicGeometry.Scheme.Modules
