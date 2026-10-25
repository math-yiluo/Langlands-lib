import Langlands.Shimura.Coefficients.Associated

noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R]

/-- Restrict sections along the product of a map of cover objects with the identity. -/
def coverPullback {Y Z : C} (a : Z ⟶ Y) (F : Sheaf J (ModuleCat.{u} R)) :
    (productSheaf J Y).obj F ⟶ (productSheaf J Z).obj F where
  hom.app U := F.obj.map (prod.map a (𝟙 U.unop)).op
  hom.naturality := by
    intro U V f
    change F.obj.map (prod.map (𝟙 Y) f.unop).op ≫
        F.obj.map (prod.map a (𝟙 V.unop)).op =
      F.obj.map (prod.map a (𝟙 U.unop)).op ≫
        F.obj.map (prod.map (𝟙 Z) f.unop).op
    simp only [← Functor.map_comp, ← op_comp, prod.map_map,
      Category.id_comp, Category.comp_id]

@[simp] theorem coverPullback_id (Y : C) (F : Sheaf J (ModuleCat.{u} R)) :
    coverPullback J (𝟙 Y) F = 𝟙 _ :=
  deckMap_id J Y F

@[reassoc] theorem coverPullback_comp {Y Z W : C} (a : Z ⟶ Y) (b : W ⟶ Z)
    (F : Sheaf J (ModuleCat.{u} R)) :
    coverPullback J (b ≫ a) F = coverPullback J a F ≫ coverPullback J b F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map (b ≫ a) (𝟙 U.unop)).op =
    F.obj.map (prod.map a (𝟙 U.unop)).op ≫ F.obj.map (prod.map b (𝟙 U.unop)).op
  rw [← F.obj.map_comp, ← op_comp, prod.map_map, Category.id_comp]

@[reassoc] theorem coverPullback_natural {Y Z : C} (a : Z ⟶ Y)
    {F E : Sheaf J (ModuleCat.{u} R)} (c : F ⟶ E) :
    coverPullback J a F ≫ (productSheaf J Z).map c =
      (productSheaf J Y).map c ≫ coverPullback J a E := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  exact c.hom.naturality _

variable {G H : Type u} [Group G] [Group H]
variable {Y : Action C G} {Z : Action C H} (φ : H →* G)
variable (a : Z ⟶ (Action.res C φ).obj Y)

/-- Restriction along an equivariant cover map intertwines deck pullbacks. -/
@[reassoc] theorem coverPullback_deck (F : Sheaf J (ModuleCat.{u} R)) (h : H) :
    deckMap J (Y.ρ (φ h)) F ≫ coverPullback J a.hom F =
      coverPullback J a.hom F ≫ deckMap J (Z.ρ h) F := by
  change coverPullback J (Y.ρ (φ h)) F ≫ coverPullback J a.hom F =
    coverPullback J a.hom F ≫ coverPullback J (Z.ρ h) F
  rw [← coverPullback_comp, ← coverPullback_comp]
  exact congrArg (fun b => coverPullback J b F) (a.comm h).symm

variable {F : Action (Sheaf J (ModuleCat.{u} R)) G}
variable {E : Action (Sheaf J (ModuleCat.{u} R)) H}
variable (c : (Action.res (Sheaf J (ModuleCat.{u} R)) φ).obj F ⟶ E)

/-- The combined cover and coefficient map intertwines the diagonal actions. -/
@[reassoc] theorem crossCover_diagonal (h : H) :
    (diagonal J Y F).ρ (φ h) ≫
        (coverPullback J a.hom F.V ≫ (productSheaf J Z.V).map c.hom) =
      (coverPullback J a.hom F.V ≫ (productSheaf J Z.V).map c.hom) ≫
        (diagonal J Z E).ρ h := by
  change (deckMap J (Y.ρ (φ h)⁻¹) F.V ≫
      (productSheaf J Y.V).map (F.ρ (φ h))) ≫ _ =
    _ ≫ (deckMap J (Z.ρ h⁻¹) E.V ≫ (productSheaf J Z.V).map (E.ρ h))
  rw [Category.assoc, ← coverPullback_natural_assoc, ← Category.assoc,
    ← map_inv φ, coverPullback_deck J φ a F.V h⁻¹]
  simp only [Category.assoc]
  have hc : F.ρ (φ h) ≫ c.hom = c.hom ≫ E.ρ h := c.comm h
  rw [← Functor.map_comp, hc, Functor.map_comp,
    ← Category.assoc (deckMap J (Z.ρ h⁻¹) F.V), deckMap_natural]
  simp only [Category.assoc]

/-- A compatible cover map and coefficient map induce a map of actual invariant sheaves. -/
def crossCoverMap : associated J Y F ⟶ associated J Z E :=
  lift J Z (inclusion J Y F ≫ coverPullback J a.hom F.V ≫
    (productSheaf J Z.V).map c.hom) (fun h => by
      rw [Category.assoc, ← crossCover_diagonal J φ a c h,
        ← Category.assoc, inclusion_invariant])

@[reassoc (attr := simp)] theorem crossCoverMap_inclusion :
    crossCoverMap J φ a c ≫ inclusion J Z E =
      inclusion J Y F ≫ coverPullback J a.hom F.V ≫ (productSheaf J Z.V).map c.hom :=
  lift_inclusion J Z _ _

/-- Identity cover and coefficient maps induce the identity on invariants. -/
@[simp] theorem crossCoverMap_id
    (Y : Action C G) (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    crossCoverMap J (MonoidHom.id G) (𝟙 Y) (𝟙 F) = 𝟙 (associated J Y F) := by
  apply hom_ext J Y
  simp

/-- On an unchanged cover and group, this is the existing coefficient functor. -/
theorem crossCoverMap_sameCover
    (Y : Action C G) {F E : Action (Sheaf J (ModuleCat.{u} R)) G} (c : F ⟶ E) :
    crossCoverMap J (MonoidHom.id G) (𝟙 Y) c = (associatedFunctor J Y).map c := by
  apply hom_ext J Y
  simp [inclusion_natural]

variable {K : Type u} [Group K] {W : Action C K}
variable {D : Action (Sheaf J (ModuleCat.{u} R)) K}

/-- Composition is contravariant in covers and covariant in coefficients. -/
@[reassoc] theorem crossCoverMap_comp (ψ : K →* H)
    (b : W ⟶ (Action.res C ψ).obj Z)
    (d : (Action.res (Sheaf J (ModuleCat.{u} R)) ψ).obj E ⟶ D) :
    crossCoverMap J φ a c ≫ crossCoverMap J ψ b d =
      crossCoverMap J (φ.comp ψ) (b ≫ (Action.res C ψ).map a)
        ((Action.res (Sheaf J (ModuleCat.{u} R)) ψ).map c ≫ d) := by
  apply hom_ext J W
  simp only [Category.assoc, crossCoverMap_inclusion, crossCoverMap_inclusion_assoc]
  change inclusion J Y F ≫ coverPullback J a.hom F.V ≫
      (productSheaf J Z.V).map c.hom ≫ coverPullback J b.hom E.V ≫
        (productSheaf J W.V).map d.hom =
    inclusion J Y F ≫ coverPullback J (b.hom ≫ a.hom) F.V ≫
      (productSheaf J W.V).map (c.hom ≫ d.hom)
  rw [coverPullback_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hn : (productSheaf J Z.V).map c.hom ≫ coverPullback J b.hom E.V =
      coverPullback J b.hom F.V ≫ (productSheaf J W.V).map c.hom :=
    (coverPullback_natural J b.hom c.hom).symm
  simpa only [Category.assoc] using congrArg
    (fun k => inclusion J Y F ≫ coverPullback J a.hom F.V ≫ k ≫
      (productSheaf J W.V).map d.hom) hn

/-- Cover change is natural in the coefficient representation. -/
def associatedCoverChange :
    associatedFunctor (R := R) J Y ⟶
      Action.res (Sheaf J (ModuleCat.{u} R)) φ ⋙ associatedFunctor J Z where
  app F := crossCoverMap J φ a (𝟙 ((Action.res _ φ).obj F))
  naturality {F E} c := by
    dsimp only [Functor.comp_map]
    apply hom_ext J Z
    simp only [Category.assoc, crossCoverMap_inclusion, inclusion_natural,
      inclusion_natural_assoc, crossCoverMap_inclusion_assoc]
    change inclusion J Y F ≫ (productSheaf J Y.V).map c.hom ≫
        coverPullback J a.hom E.V ≫ (productSheaf J Z.V).map (𝟙 E.V) =
      inclusion J Y F ≫ coverPullback J a.hom F.V ≫
        (productSheaf J Z.V).map (𝟙 F.V) ≫ (productSheaf J Z.V).map c.hom
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    exact congrArg (fun k => inclusion J Y F ≫ k) (coverPullback_natural J a.hom c.hom).symm

/-- Constant coefficients use the same map between actual invariant sheaves. -/
def constantCrossCoverMap [HasSheafify J (ModuleCat.{u} R)]
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (constantAssociatedFunctor J Y).obj M ⟶ (constantAssociatedFunctor J Z).obj N :=
  crossCoverMap J φ a
    (F := ((constantSheaf J (ModuleCat.{u} R)).mapAction G).obj M)
    (((constantSheaf J (ModuleCat.{u} R)).mapAction H).map c)

@[simp] theorem constantCrossCoverMap_id [HasSheafify J (ModuleCat.{u} R)]
    (Y : Action C G) (M : Action (ModuleCat.{u} R) G) :
    constantCrossCoverMap J (MonoidHom.id G) (𝟙 Y) (𝟙 M) =
      𝟙 ((constantAssociatedFunctor J Y).obj M) := by
  apply hom_ext J Y
  simp only [constantCrossCoverMap, crossCoverMap_inclusion, Action.id_hom,
    Functor.mapAction_map_hom, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, coverPullback_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Constant coefficient maps retain the cover and group composition law. -/
@[reassoc] theorem constantCrossCoverMap_comp [HasSheafify J (ModuleCat.{u} R)]
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    {P : Action (ModuleCat.{u} R) K}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N)
    (ψ : K →* H) (b : W ⟶ (Action.res C ψ).obj Z)
    (d : (Action.res (ModuleCat.{u} R) ψ).obj N ⟶ P) :
    constantCrossCoverMap J φ a c ≫ constantCrossCoverMap J ψ b d =
      constantCrossCoverMap J (φ.comp ψ) (b ≫ (Action.res C ψ).map a)
        ((Action.res (ModuleCat.{u} R) ψ).map c ≫ d) := by
  simp only [constantCrossCoverMap, Functor.map_comp]
  exact crossCoverMap_comp J φ a _ ψ b _

end Langlands.Shimura.Coefficients
