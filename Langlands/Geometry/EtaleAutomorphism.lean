import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Automorphisms of a scheme acting on its small étale site

An automorphism `σ` of a scheme `Y` acts on the small étale site of `Y` by
composing structure morphisms with `σ`. This is an equivalence of sites, so
precomposition with it is an equivalence of the categories of étale sheaves.
It preserves global sections.
-/

noncomputable section

namespace Langlands.Geometry.EtaleAutomorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}}

/-- Composing structure morphisms of étale `Y`-schemes with an automorphism of
`Y`. -/
abbrev siteMap (σ : Y ≅ Y) : Y.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : Etale σ.hom)

/-- Composing with an automorphism is an equivalence of the small étale
category, with inverse the composition with the inverse automorphism. -/
def siteEquivalence (σ : Y ≅ Y) : Y.Etale ≌ Y.Etale :=
  CategoryTheory.Equivalence.mk (siteMap σ) (siteMap σ.symm)
    ((MorphismProperty.Over.mapId ⊤ Y).symm ≪≫
      MorphismProperty.Over.mapComp ⊤ _ _ (𝟙 Y) (by simp))
    ((MorphismProperty.Over.mapComp ⊤ _ _ (𝟙 Y) (by simp)).symm ≪≫
      MorphismProperty.Over.mapId ⊤ Y)

/-- Covering sieves of the small étale site, pointwise: every point of the
underlying scheme lifts along an arrow of the sieve. -/
theorem mem_smallEtaleTopology_iff {U : Y.Etale} (S : Sieve U) :
    S ∈ Y.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (V : Y.Etale) (f : V ⟶ U) (v : V.left), S f ∧ f.left v = x := by
  have e : Y.smallEtaleTopology = Y.smallEtalePretopology.toGrothendieck :=
    Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology Y le_rfl
  rw [e]
  refine (Scheme.mem_toGrothendieck_smallPretopology U S).trans ?_
  refine forall_congr' fun x => ?_
  constructor
  · rintro ⟨V, f, v, hf, -, hv⟩
    exact ⟨V, f, v, hf, hv⟩
  · rintro ⟨V, f, v, hf, hv⟩
    exact ⟨V, f, v, hf, inferInstance, hv⟩

/-- Composing with an automorphism is cocontinuous for the small étale
topology. A lift of a point along an arrow into the translated object is
translated back. -/
instance siteMap_isCocontinuous (σ : Y ≅ Y) :
    (siteMap σ).IsCocontinuous Y.smallEtaleTopology Y.smallEtaleTopology where
  cover_lift {U S} hS := by
    rw [mem_smallEtaleTopology_iff] at hS ⊢
    intro x
    obtain ⟨V, f, v, hf, hv⟩ := hS x
    let V' : Y.Etale := MorphismProperty.Over.mk ⊤ (V.hom ≫ σ.inv) inferInstance
    have hw : f.left ≫ U.hom = V'.hom := by
      have h := f.w
      simp only [Functor.const_obj_obj, Functor.id_obj, Functor.id_map,
        CategoryTheory.Functor.const_obj_map, Category.comp_id] at h
      simp only [V', MorphismProperty.Over.mk_hom, ← h, MorphismProperty.Over.map_obj_hom]
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    let f' : V' ⟶ U := MorphismProperty.Over.homMk f.left hw
    let e : (siteMap σ).obj V' ⟶ V :=
      MorphismProperty.Over.homMk (𝟙 V.left) (by
        dsimp [V']
        rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    refine ⟨V', f', v, ?_, hv⟩
    have hcomp : (siteMap σ).map f' = e ≫ f := by
      apply MorphismProperty.Over.Hom.ext
      show f.left = 𝟙 V.left ≫ f.left
      exact (Category.id_comp f.left).symm
    change S ((siteMap σ).map f')
    rw [hcomp]
    exact S.downward_closed hf e

instance (σ : Y ≅ Y) :
    (siteEquivalence σ).functor.IsCocontinuous Y.smallEtaleTopology Y.smallEtaleTopology :=
  siteMap_isCocontinuous σ

instance (σ : Y ≅ Y) :
    (siteEquivalence σ).inverse.IsCocontinuous Y.smallEtaleTopology Y.smallEtaleTopology :=
  siteMap_isCocontinuous σ.symm

instance (σ : Y ≅ Y) :
    (siteEquivalence σ).inverse.IsDenseSubsite Y.smallEtaleTopology Y.smallEtaleTopology :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

variable (A : Type*) [Category A]

/-- An automorphism `σ` of `Y` acts on étale sheaves by precomposition with
`siteMap σ`: the translated sheaf has sections `F(U, u ≫ σ)` over `(U, u)`. -/
def sheafEquivalence (σ : Y ≅ Y) :
    Sheaf Y.smallEtaleTopology A ≌ Sheaf Y.smallEtaleTopology A :=
  (siteEquivalence σ.symm).sheafCongr Y.smallEtaleTopology Y.smallEtaleTopology A

/-- The translation functor of an automorphism on étale sheaves. -/
abbrev translate (σ : Y ≅ Y) : Sheaf Y.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  (sheafEquivalence A σ).functor

instance (σ : Y ≅ Y) : (translate A σ).IsEquivalence :=
  inferInstanceAs (sheafEquivalence A σ).functor.IsEquivalence

/-- Translating by `σ` and then by `τ` is translating by the composite
automorphism `τ ≪≫ σ`, whose underlying morphism is `τ.hom ≫ σ.hom`. -/
def translateComp (σ τ : Y ≅ Y) :
    translate A σ ⋙ translate A τ ≅ translate A (τ ≪≫ σ) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale τ.hom)
        (inferInstance : Etale σ.hom))) F.obj))
    (fun {F G} φ => by
      apply Sheaf.hom_ext
      ext U
      exact (φ.hom.naturality _).symm)

/-- Translating by the identity automorphism is the identity. -/
def translateId : translate A (Iso.refl Y) ≅ 𝟭 (Sheaf Y.smallEtaleTopology A) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (MorphismProperty.Over.mapId ⊤ Y)).symm F.obj ≪≫ F.obj.leftUnitor))
    (fun {F G} φ => by
      apply Sheaf.hom_ext
      ext U
      dsimp
      simp only [Category.comp_id]
      exact (φ.hom.naturality _).symm)

/-- An automorphism carries the terminal object of the small étale site to a
terminal object. -/
def terminalIso (σ : Y ≅ Y) : (siteMap σ).obj (⊤_ Y.Etale) ≅ ⊤_ Y.Etale :=
  (IsTerminal.isTerminalObj (siteEquivalence σ).functor _ terminalIsTerminal).uniqueUpToIso
    terminalIsTerminal

/-- Translation preserves sections over the terminal object. -/
def sectionsIso (σ : Y ≅ Y) :
    translate A σ ⋙ (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)) ≅
      (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)) :=
  NatIso.ofComponents (fun F => (F.obj.mapIso (terminalIso σ).op).symm)
    (fun φ => (φ.hom.naturality (terminalIso σ).inv.op).symm)

/-- Equal automorphisms give isomorphic translation functors, with identity
components on sections. -/
def translateCongr {σ τ : Y ≅ Y} (h : σ = τ) : translate A σ ≅ translate A τ :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (MorphismProperty.Over.mapCongr ⊤ (congrArg Iso.hom h)
        (inferInstance : Etale σ.hom))).symm F.obj))
    (fun φ => by
      apply Sheaf.hom_ext
      ext U
      exact (φ.hom.naturality _).symm)

/-- Composing with an automorphism carries terminal objects of the small étale
category to terminal objects. -/
def isTerminalSiteMapObj (σ : Y ≅ Y) {X : Y.Etale} (hX : IsTerminal X) :
    IsTerminal ((siteMap σ).obj X) :=
  IsTerminal.isTerminalObj (siteEquivalence σ).functor _ hX

/-- Translation isomorphisms of sections are compatible with composition of
automorphisms. Both sides are restrictions along arrows from the terminal
object into a terminal object. -/
theorem sectionsIso_comp (σ τ : Y ≅ Y) (F : Sheaf Y.smallEtaleTopology A) :
    (sectionsIso A τ).hom.app ((translate A σ).obj F) ≫ (sectionsIso A σ).hom.app F =
      ((sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale))).map
          ((translateComp A σ τ).hom.app F) ≫ (sectionsIso A (τ ≪≫ σ)).hom.app F := by
  dsimp [sectionsIso, translateComp]
  erw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (isTerminalSiteMapObj σ (isTerminalSiteMapObj τ terminalIsTerminal)).hom_ext _ _

/-- Translation isomorphisms of sections are compatible with equalities of
automorphisms. -/
theorem sectionsIso_congr {σ τ : Y ≅ Y} (h : σ = τ) (F : Sheaf Y.smallEtaleTopology A) :
    (sectionsIso A σ).hom.app F =
      ((sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale))).map
          ((translateCongr A h).hom.app F) ≫ (sectionsIso A τ).hom.app F := by
  dsimp [sectionsIso, translateCongr]
  erw [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (isTerminalSiteMapObj σ terminalIsTerminal).hom_ext _ _

/-- Translation isomorphisms of sections are compatible with the identity
automorphism. -/
theorem sectionsIso_id (F : Sheaf Y.smallEtaleTopology A) :
    (sectionsIso A (Iso.refl Y)).hom.app F =
      ((sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale))).map
        ((translateId A).hom.app F) := by
  dsimp [sectionsIso, translateId]
  simp only [Category.comp_id]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (isTerminalSiteMapObj (Iso.refl Y) terminalIsTerminal).hom_ext _ _

section Linear

variable (R : Type u) [CommRing R]

/-- Translation of module sheaves is additive. -/
instance translate_additive (σ : Y ≅ Y) : (translate (ModuleCat.{u} R) σ).Additive where
  map_add := by
    intros
    apply Sheaf.hom_ext
    rfl


instance translate_preservesInjectiveObjects (σ : Y ≅ Y) :
    (translate (ModuleCat.{u} R) σ).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_isEquivalence

/-- Translation of module sheaves is `R`-linear. -/
instance translate_linear (σ : Y ≅ Y) : (translate (ModuleCat.{u} R) σ).Linear R where
  map_smul f r := by
    apply Sheaf.hom_ext
    rfl

end Linear

end Langlands.Geometry.EtaleAutomorphism
