/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Extensions by zero of constant sheaves generate

Every étale sheaf of `Λ`-modules `F` on `X` is a quotient of a direct sum of extensions by zero
`v_! Λ` along étale maps `v : V ⟶ X` from affine schemes [Stacks 093C]: a section `σ ∈ F(V)`
is a map `v_! Λ ⟶ F`, and maps out of `F` are determined by their values on sections over
affine étale `X`-schemes. This is the first step of the presentation of constructible sheaves
[Stacks 095N] used for `AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The adjunction `v_! ⊣ v^*` for an étale `X`-scheme `V`, with `v^*` the restriction of
sections. -/
noncomputable def Etale.etaleLowerShriekLocalizationAdjunction {W : Scheme.{u}} (v : W ⟶ X)
    (h : Etale v) :
    Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v h ⊣
      Etale.localizationRestriction (ModuleCat.{u + 1} Λ) v h :=
  have : (MorphismProperty.Over.map ⊤ h).IsContinuous W.smallEtaleTopology
      X.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
      (W.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale))
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    (ModuleCat.{u + 1} Λ) W.smallEtaleTopology X.smallEtaleTopology

/-- The étale `X`-scheme `v : W ⟶ X`, as the image of the terminal étale `W`-scheme. -/
noncomputable abbrev Etale.self {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) : X.Etale :=
  (MorphismProperty.Over.map ⊤ h).obj (Scheme.Etale.mk (𝟙 W))

/-- The map `v_! Λ ⟶ F` corresponding to a section `σ` of `F` over `v : W ⟶ X`. -/
noncomputable def Etale.sectionHom (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) (σ : F.obj.obj (op (Etale.self v h))) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v h).obj
      ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ⟶ F :=
  ((Etale.etaleLowerShriekLocalizationAdjunction v h).homEquiv _ _).symm
    (((constantSheafAdj W.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (MorphismProperty.Over.mkIdTerminal @Etale W)).homEquiv _ _).symm
        (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ σ)))

lemma Etale.sectionHom_comp {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : F ⟶ G)
    {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) (σ : F.obj.obj (op (Etale.self v h))) :
    Etale.sectionHom F v h σ ≫ g = Etale.sectionHom G v h (g.hom.app _ σ) := by
  rw [Etale.sectionHom, Etale.sectionHom, ← Adjunction.homEquiv_naturality_right_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 2
  ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply]
  erw [LinearMap.toSpanSingleton_apply, one_smul, LinearMap.toSpanSingleton_apply, one_smul]
  rfl

lemma Etale.sectionHom_injective (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) :
    Function.Injective (Etale.sectionHom F v h) := by
  intro σ σ' hσ
  have := congr(ConcreteCategory.hom
    ((((constantSheafAdj W.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (MorphismProperty.Over.mkIdTerminal @Etale W)).homEquiv _ _)
        (((Etale.etaleLowerShriekLocalizationAdjunction v h).homEquiv _ _) $hσ))) (1 : Λ))
  simp only [Etale.sectionHom, Equiv.apply_symm_apply, ModuleCat.hom_ofHom] at this
  erw [LinearMap.toSpanSingleton_apply, one_smul, LinearMap.toSpanSingleton_apply, one_smul] at this
  exact this

/-- Étale sheaves of `Λ`-modules have coproducts indexed by types of size `u + 1`. -/
instance (X : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  IsGrothendieckAbelian.hasColimits _

/-- The index of the generators of `F`: sections of `F` over affine étale `X`-schemes. -/
abbrev Etale.SectionIndex (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Σ V : {V : X.Etale // IsAffine V.left}, F.obj.obj (op (Etale.self (X := X) V.1.hom V.1.prop))

/-- Morphisms out of an étale sheaf agreeing on sections over affine étale `X`-schemes agree. -/
lemma Etale.sheafHom_ext_of_isAffine {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {g g' : F ⟶ G} (h : ∀ (V : X.Etale), IsAffine V.left → ∀ σ : F.obj.obj (op V),
      g.hom.app (op V) σ = g'.hom.app (op V) σ) : g = g' := by
  have hG := (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology G.obj
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).1 G.property
  rw [isSheaf_iff_isSheaf_of_type] at hG
  ext U τ
  let S : Sieve U.unop :=
    { arrows := fun W f ↦ G.obj.map f.op (g.hom.app U τ) = G.obj.map f.op (g'.hom.app U τ)
      downward_closed := fun {W W'} f hf k ↦ by
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rw [hf] }
  have hS : S ∈ X.smallEtaleTopology U.unop := by
    refine (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
    obtain ⟨A, hA, hxA, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : U.unop.left.Opens) from trivial)
    let VA : X.Etale := MorphismProperty.Over.mk ⊤ (A.ι ≫ U.unop.hom)
      (MorphismProperty.comp_mem _ _ _ inferInstance U.unop.prop)
    let f : VA ⟶ U.unop := MorphismProperty.Over.homMk A.ι rfl trivial
    refine ⟨VA, f, ?_, ⟨x, hxA⟩, rfl⟩
    have : IsAffine VA.left := hA
    change G.obj.map f.op (g.hom.app U τ) = G.obj.map f.op (g'.hom.app U τ)
    rw [← NatTrans.naturality_apply g.hom f.op, ← NatTrans.naturality_apply g'.hom f.op]
    exact h VA this _
  exact (hG S hS).isSeparatedFor.ext fun W f hf ↦ hf

/-- **Extensions by zero of constant sheaves generate** (Stacks 093C). Every étale sheaf of
`Λ`-modules `F` is a quotient of the direct sum, over the sections `σ` of `F` over affine étale
`X`-schemes `v : V ⟶ X`, of the extensions by zero `v_! Λ`. -/
@[stacks 093C]
theorem Etale.epi_sigmaDesc_sectionHom (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Epi (Sigma.desc fun i : Etale.SectionIndex F ↦
      Etale.sectionHom F i.1.1.hom i.1.1.prop i.2) := by
  refine ⟨fun {G} g g' hgg' ↦ Etale.sheafHom_ext_of_isAffine fun V hV σ ↦ ?_⟩
  -- the étale `X`-scheme `V` is isomorphic to the image of the terminal étale `V`-scheme
  let e : Etale.self (X := X) V.hom V.prop ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  have key (τ : F.obj.obj (op (Etale.self (X := X) V.hom V.prop))) :
      g.hom.app _ τ = g'.hom.app _ τ := by
    have := congr(Sigma.ι _ (⟨⟨V, hV⟩, τ⟩ : Etale.SectionIndex F) ≫ $hgg')
    simp only [Sigma.ι_comp_desc_assoc, Etale.sectionHom_comp] at this
    exact Etale.sectionHom_injective _ _ _ this
  apply (ConcreteCategory.bijective_of_isIso (G.obj.map e.hom.op)).1
  rw [← NatTrans.naturality_apply g.hom e.hom.op, ← NatTrans.naturality_apply g'.hom e.hom.op]
  exact key _

end AlgebraicGeometry
