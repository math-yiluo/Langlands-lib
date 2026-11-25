/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation

/-!
# The free extension presentation of an etale torsor

Source: Stacks Project, Tag 03AJ, the free abelian sheaf construction
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u})
variable {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : Torsor G)

namespace EtaleFreeExtension

/-- The free abelian sheaf on the sections of the torsor. -/
private noncomputable abbrev freeSheaf :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (T.sheaf.obj ⋙ AddCommGrpCat.free)

/-- The free abelian sheaf on pairs of sections. -/
private noncomputable abbrev relations :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (T.pairs ⋙ AddCommGrpCat.free)

/-- The relation sending `(x,y)` to `[y]-[x]`. -/
private noncomputable abbrev difference : relations X T ⟶ freeSheaf X T :=
  (presheafToSheaf _ _).map T.pairsDiff

/-- The relation sending `(x,y)` to the unique `g` with `g +ᵥ x = y`. -/
private noncomputable def displacement : relations X T ⟶ G :=
  ⟨sheafifyLift _ T.pairsSub G.property⟩

/-- The quotient of `G ⊕ ℤ[T]` by `[y]-[x] = y-x`, formed as a pushout. -/
private noncomputable abbrev extension := pushout (difference X T) (displacement X T)

/-- The inclusion of the coefficient sheaf in the presented extension. -/
private noncomputable abbrev inclusion : G ⟶ extension X T :=
  pushout.inr (difference X T) (displacement X T)

/-- The map of the free generators to the presented extension. -/
private noncomputable abbrev generators : freeSheaf X T ⟶ extension X T :=
  pushout.inl (difference X T) (displacement X T)

/-- The constant integer presheaf, in the coefficient universe of the torsor. -/
private abbrev integers : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ))

/-- Augmentation of the free abelian presheaf. -/
private def augmentation : T.sheaf.obj ⋙ AddCommGrpCat.free ⟶ integers X where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ ↦ (⟨1⟩ : ULift.{u + 1, 0} ℤ))
  naturality U V f := by
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun t ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of t)) = _
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
    rfl

private lemma difference_augmentation : T.pairsDiff ≫ augmentation X T = 0 := by
  ext U : 2
  ext : 1
  refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p)) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub, _root_.sub_self]

/-- Augmentation of the free abelian sheaf. -/
private noncomputable abbrev degree : freeSheaf X T ⟶
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) :=
  (presheafToSheaf _ _).map (augmentation X T)

/-- The pair-difference relation has degree zero. -/
private lemma difference_degree : difference X T ≫ degree X T = 0 := by
  rw [← Functor.map_comp, difference_augmentation]
  exact (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_zero _ _

/-- The degree of a section of the presented extension. -/
private noncomputable def projection : extension X T ⟶
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) :=
  pushout.desc (degree X T) 0 (by rw [difference_degree, comp_zero])

/-- The coefficient sheaf lies in degree zero. -/
private lemma inclusion_projection : inclusion X T ≫ projection X T = 0 := by
  apply pushout.inr_desc

/-- A local section of the torsor gives a degree-one section of the extension. -/
private noncomputable def generator (U : X.Etaleᵒᵖ) (t : T.sheaf.obj.obj U) :
    (extension X T).obj.obj U :=
  (generators X T).hom.app U
    ((toSheafify X.smallEtaleTopology
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (FreeAbelianGroup.of t))

end EtaleFreeExtension

private lemma free_generator_naturality (X : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : G.Torsor)
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (t : T.sheaf.obj.obj U) :
    (EtaleFreeExtension.extension X T).obj.map f
      (EtaleFreeExtension.generator X T U t) =
        EtaleFreeExtension.generator X T V (T.sheaf.obj.map f t) := by
  unfold EtaleFreeExtension.generator
  have h₁ := congr_arg (fun η ↦ η
    ((toSheafify X.smallEtaleTopology
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (FreeAbelianGroup.of t)))
    ((EtaleFreeExtension.generators X T).hom.naturality f)
  have h₂ := congr_arg (fun η ↦ η (FreeAbelianGroup.of t))
    ((toSheafify X.smallEtaleTopology
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).naturality f)
  change (EtaleFreeExtension.generators X T).hom.app V
    ((EtaleFreeExtension.freeSheaf X T).obj.map f _) = _ at h₁
  change (toSheafify X.smallEtaleTopology
    (T.sheaf.obj ⋙ AddCommGrpCat.free)).app V
    (FreeAbelianGroup.map (T.sheaf.obj.map f) (FreeAbelianGroup.of t)) = _ at h₂
  rw [FreeAbelianGroup.map_of_apply] at h₂
  exact h₁.symm.trans (congr_arg ((EtaleFreeExtension.generators X T).hom.app V) h₂.symm)

private lemma free_generator_degree (X : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : G.Torsor)
    (U : X.Etaleᵒᵖ) (t : T.sheaf.obj.obj U) :
    (EtaleFreeExtension.projection X T).hom.app U
      (EtaleFreeExtension.generator X T U t) =
        (toSheafify X.smallEtaleTopology
          (EtaleFreeExtension.integers X)).app U ⟨1⟩ := by
  unfold EtaleFreeExtension.generator
  change ((EtaleFreeExtension.generators X T ≫
    EtaleFreeExtension.projection X T).hom.app U) _ = _
  unfold EtaleFreeExtension.projection
  rw [pushout.inl_desc]
  have h := congr_arg (fun η ↦ η.app U (FreeAbelianGroup.of t))
    (toSheafify_naturality X.smallEtaleTopology
      (EtaleFreeExtension.augmentation X T))
  exact h.symm

private lemma free_generator_vadd (X : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : G.Torsor)
    (U : X.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
    EtaleFreeExtension.generator X T U (T.vadd U g t) =
      EtaleFreeExtension.generator X T U t +
        (EtaleFreeExtension.inclusion X T).hom.app U g := by
  have h := congr_arg (fun η ↦ η.hom.app U
    ((toSheafify X.smallEtaleTopology
      (T.pairs ⋙ AddCommGrpCat.free)).app U
        (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U))))
    (pushout.condition (f := EtaleFreeExtension.difference X T)
      (g := EtaleFreeExtension.displacement X T))
  have hd := congr_arg (fun η ↦ η.app U
    (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U)))
    (toSheafify_naturality X.smallEtaleTopology T.pairsDiff)
  have hs := congr_arg (fun η ↦ η.app U
    (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U)))
    (toSheafify_sheafifyLift X.smallEtaleTopology T.pairsSub G.property)
  change (EtaleFreeExtension.generators X T).hom.app U
    ((EtaleFreeExtension.difference X T).hom.app U _) =
      (EtaleFreeExtension.inclusion X T).hom.app U
        ((EtaleFreeExtension.displacement X T).hom.app U _) at h
  change (toSheafify X.smallEtaleTopology
    (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (T.pairsDiff.app U _) =
      (EtaleFreeExtension.difference X T).hom.app U
        ((toSheafify X.smallEtaleTopology
          (T.pairs ⋙ AddCommGrpCat.free)).app U _) at hd
  change (EtaleFreeExtension.displacement X T).hom.app U
    ((toSheafify X.smallEtaleTopology
      (T.pairs ⋙ AddCommGrpCat.free)).app U _) = T.pairsSub.app U _ at hs
  rw [← hd, hs] at h
  change (EtaleFreeExtension.generators X T).hom.app U
    ((toSheafify X.smallEtaleTopology
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U
      (FreeAbelianGroup.lift _ (FreeAbelianGroup.of _))) =
        (EtaleFreeExtension.inclusion X T).hom.app U
          (FreeAbelianGroup.lift _ (FreeAbelianGroup.of _)) at h
  simp only [FreeAbelianGroup.lift_apply_of, Torsor.sub_vadd_eq, map_sub] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private def freeLift (X : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : Torsor G)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (j : ∀ U : X.Etaleᵒᵖ, T.sheaf.obj.obj U → A.obj.obj U)
    (hn : ∀ ⦃U V : X.Etaleᵒᵖ⦄ (f : U ⟶ V) (t : T.sheaf.obj.obj U),
      A.obj.map f (j U t) = j V (T.sheaf.obj.map f t)) :
    T.sheaf.obj ⋙ AddCommGrpCat.free ⟶ A.obj where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (j U))
  naturality U V f := by
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun t ↦ ?_
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of t)) = _
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
    simpa only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      FreeAbelianGroup.lift_apply_of] using (hn f t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem freeUniversal (X : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : Torsor G)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (k : G ⟶ A)
    (j : ∀ U : X.Etaleᵒᵖ, T.sheaf.obj.obj U → A.obj.obj U)
    (hn : ∀ ⦃U V : X.Etaleᵒᵖ⦄ (f : U ⟶ V) (t : T.sheaf.obj.obj U),
      A.obj.map f (j U t) = j V (T.sheaf.obj.map f t))
    (ha : ∀ U (g : G.obj.obj U) (t : T.sheaf.obj.obj U),
      j U (T.vadd U g t) = j U t + k.hom.app U g) :
    ∃! l : EtaleFreeExtension.extension X T ⟶ A,
      EtaleFreeExtension.inclusion X T ≫ l = k ∧
        ∀ U t, l.hom.app U (EtaleFreeExtension.generator X T U t) = j U t := by
  let β := freeLift X T A j hn
  let b : EtaleFreeExtension.freeSheaf X T ⟶ A :=
    ⟨sheafifyLift X.smallEtaleTopology β A.property⟩
  have hb : toSheafify X.smallEtaleTopology _ ≫ b.hom = β :=
    toSheafify_sheafifyLift _ _ _
  have hrel : EtaleFreeExtension.difference X T ≫ b =
      EtaleFreeExtension.displacement X T ≫ k := by
    ext1
    apply sheafify_hom_ext X.smallEtaleTopology _ _ A.property
    change toSheafify X.smallEtaleTopology _ ≫
      (EtaleFreeExtension.difference X T).hom ≫ b.hom =
        toSheafify X.smallEtaleTopology _ ≫
          (EtaleFreeExtension.displacement X T).hom ≫ k.hom
    rw [← toSheafify_naturality_assoc]
    change T.pairsDiff ≫ (toSheafify X.smallEtaleTopology _ ≫ b.hom) = _
    rw [hb]
    change T.pairsDiff ≫ β =
      toSheafify X.smallEtaleTopology _ ≫
        sheafifyLift X.smallEtaleTopology T.pairsSub G.property ≫ k.hom
    rw [← Category.assoc, toSheafify_sheafifyLift]
    ext U : 2
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun p ↦ ?_
    change β.app U (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p)) =
      k.hom.app U (FreeAbelianGroup.lift _ (FreeAbelianGroup.of p))
    simp only [FreeAbelianGroup.lift_apply_of, map_sub]
    dsimp only [β, freeLift]
    simp only [AddCommGrpCat.hom_ofHom]
    erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
    change j U p.2 - j U p.1 = k.hom.app U (T.sub p.1 p.2)
    have hh := ha U (T.sub p.1 p.2) p.1
    rw [T.sub_vadd] at hh
    rw [hh]
    abel
  let l : EtaleFreeExtension.extension X T ⟶ A := pushout.desc b k hrel
  have hl : EtaleFreeExtension.inclusion X T ≫ l = k := pushout.inr_desc _ _ _
  have hj (U : X.Etaleᵒᵖ) (t : T.sheaf.obj.obj U) :
      l.hom.app U (EtaleFreeExtension.generator X T U t) = j U t := by
    change ((EtaleFreeExtension.generators X T ≫ l).hom.app U) _ = _
    rw [show EtaleFreeExtension.generators X T ≫ l = b from pushout.inl_desc _ _ _]
    have h := congrArg (fun η ↦ η.app U (FreeAbelianGroup.of t)) hb
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, β, freeLift,
      AddCommGrpCat.hom_ofHom, AddCommGrpCat.ofHom_apply] using
      h.trans (FreeAbelianGroup.lift_apply_of (j U) t)
  refine ⟨l, ⟨hl, hj⟩, ?_⟩
  intro l' hl'
  apply pushout.hom_ext
  · ext1
    apply sheafify_hom_ext X.smallEtaleTopology _ _ A.property
    ext U : 2
    ext : 1
    refine FreeAbelianGroup.lift_ext _ _ fun t ↦ ?_
    change l'.hom.app U (EtaleFreeExtension.generator X T U t) =
      l.hom.app U (EtaleFreeExtension.generator X T U t)
    rw [hl'.2, hj]
  · exact hl'.1.trans hl.symm

/-- The free abelian sheaf on a torsor, with its translation relations imposed,
has the universal extension presentation.
Source: Stacks Project, Tag 03AJ, free-extension construction.
Proof: sheafify the free abelian presheaf of torsor sections and push out the
pair-difference morphism against torsor displacement. Augmentation kills pair
differences and sends each generator to one. Naturality follows from sheafification;
the pair relation gives translation equivariance. For the universal property, extend
the prescribed generator map by the free abelian group adjunction and sheafification.
Equivariance says exactly that pair differences agree with displacement followed by
the coefficient map, so the pushout gives the unique required morphism.
(auxiliary; not a blueprint node) -/
theorem nonempty_extensionPresentation (X : Scheme.{u})
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (T : Torsor G) :
    Nonempty (ExtensionPresentation.{u, u} X T) := by
  exact ⟨{
    middle := EtaleFreeExtension.extension X T
    inclusion := EtaleFreeExtension.inclusion X T
    generator := EtaleFreeExtension.generator X T
    generator_natural := free_generator_naturality X T
    generator_vadd := free_generator_vadd X T
    universal := freeUniversal X T
    projection := EtaleFreeExtension.projection X T
    inclusion_projection := EtaleFreeExtension.inclusion_projection X T
    projection_generator := free_generator_degree X T }⟩

end CategoryTheory.Sheaf.Torsor
