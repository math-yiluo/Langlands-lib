import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableDiscrete

/-! # Natural maps between free globally lifted representables -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

open CategoryTheory Opposite
open Langlands.Cohomology.SiteCech

universe u v z w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type z} [Group G] {ρ : G →* Aut X}
variable {L M N : GlobalLift (P := P) (ρ := ρ)}

/-- An ordinary arrow intertwines the two specified full lifted actions. -/
def IsEquivariant (p : L.obj ⟶ M.obj) : Prop :=
  ∀ g : G, (L.action g).unop ≫ (ι P ρ).map p =
    (ι P ρ).map p ≫ (M.action g).unop

@[simp]
theorem isEquivariant_id (L : GlobalLift (P := P) (ρ := ρ)) :
    IsEquivariant (L := L) (M := L) (𝟙 L.obj) := by
  intro g
  change (L.action g).unop ≫ 𝟙 _ = 𝟙 _ ≫ (L.action g).unop
  simp only [Category.comp_id, Category.id_comp]

theorem IsEquivariant.comp {p : L.obj ⟶ M.obj} {q : M.obj ⟶ N.obj}
    (hp : IsEquivariant (L := L) (M := M) p)
    (hq : IsEquivariant (L := M) (M := N) q) :
    IsEquivariant (L := L) (M := N) (p ≫ q) := by
  intro g
  rw [Functor.map_comp, ← Category.assoc, hp g, Category.assoc, hq g]
  exact (Category.assoc _ _ _).symm

/-- Normalizing a twisted restriction commutes with equivariant
postcomposition. -/
theorem precomp_postcomp (p : L.obj ⟶ M.obj) (hp : IsEquivariant p)
    {V W : TwistedOver P ρ} (f : V ⟶ W) (k : W.obj ⟶ L.obj) :
    M.precomp f (k ≫ p) = L.precomp f k ≫ p := by
  apply MorphismProperty.Over.Hom.ext
  have h := congrArg Hom.left (hp (Hom.twist f))
  change Hom.left (L.action (Hom.twist f)).unop ≫ p.left =
    p.left ≫ Hom.left (M.action (Hom.twist f)).unop at h
  change Hom.left f ≫ (k.left ≫ p.left) ≫
      Hom.left (M.action (Hom.twist f)).unop =
    (Hom.left f ≫ k.left ≫ Hom.left (L.action (Hom.twist f)).unop) ≫ p.left
  simp only [Category.assoc]
  rw [h]

variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- Postcomposition by an equivariant arrow, on the actual normalized
ordinary-Hom-valued presheaves. -/
def presheafMap (p : L.obj ⟶ M.obj) (hp : IsEquivariant p) :
    L.presheaf ⟶ M.presheaf where
  app V := ↾fun k => equivShrink _ ((equivShrink _).symm k ≫ p)
  naturality V W f := by
    apply ConcreteCategory.ext_apply
    intro k
    change equivShrink _ ((equivShrink _).symm
      (equivShrink _ (L.precomp f.unop ((equivShrink _).symm k))) ≫ p) =
      equivShrink _ (M.precomp f.unop ((equivShrink _).symm
        (equivShrink _ ((equivShrink _).symm k ≫ p))))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, precomp_postcomp p hp]

@[simp]
theorem presheafMap_id (L : GlobalLift (P := P) (ρ := ρ)) :
    presheafMap (𝟙 L.obj) (isEquivariant_id L) = 𝟙 L.presheaf := by
  ext V k
  change Shrink.{w} (V.unop.obj ⟶ L.obj) at k
  change equivShrink _ ((equivShrink _).symm k ≫ 𝟙 L.obj) = k
  rw [Category.comp_id, Equiv.apply_symm_apply]

theorem presheafMap_comp (p : L.obj ⟶ M.obj) (q : M.obj ⟶ N.obj)
    (hp : IsEquivariant p) (hq : IsEquivariant q) :
    presheafMap (p ≫ q) (hp.comp hq) =
      presheafMap p hp ≫ presheafMap q hq := by
  ext V k
  change equivShrink _ ((equivShrink _).symm k ≫ (p ≫ q)) =
    equivShrink _ ((equivShrink _).symm
      (equivShrink _ ((equivShrink _).symm k ≫ p)) ≫ q)
  rw [Equiv.symm_apply_apply, Category.assoc]

/-- Ordinary restriction identifies the induced map with the actual
Yoneda map of the given ordinary arrow. -/
theorem presheafMap_restriction (p : L.obj ⟶ M.obj) (hp : IsEquivariant p) :
    Functor.whiskerLeft (ι P ρ).op (presheafMap p hp) ≫ M.restrictionIso.hom =
      L.restrictionIso.hom ≫ shrinkYoneda.{w}.map p := by
  rfl

/-- Precomposition of a represented map restricts its fixed section along
the given equivariant ordinary arrow. -/
theorem homEquivFixedSections_naturality_left_val
    (p : L.obj ⟶ M.obj) (hp : IsEquivariant p)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ Type w) (α : M.presheaf ⟶ F) :
    (L.homEquivFixedSections F (presheafMap p hp ≫ α)).val =
      F.map ((ι P ρ).map p).op (M.homEquivFixedSections F α).val := by
  change α.app (op ((ι P ρ).obj L.obj)) (equivShrink _ ((equivShrink _).symm
    (equivShrink _ (𝟙 L.obj)) ≫ p)) = _
  rw [Equiv.symm_apply_apply, Category.id_comp]
  have h := ConcreteCategory.congr_hom (α.naturality ((ι P ρ).map p).op)
    (equivShrink _ (𝟙 M.obj))
  change α.app _ (equivShrink _ (M.precomp ((ι P ρ).map p)
    ((equivShrink _).symm (equivShrink _ (𝟙 M.obj))))) =
      F.map ((ι P ρ).map p).op
        (α.app _ (equivShrink _ (𝟙 M.obj))) at h
  rw [Equiv.symm_apply_apply, precomp_plain, Category.comp_id] at h
  exact h

section Sheaf

variable [P.RespectsIso]
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- The free sheaf map induced by an equivariant ordinary arrow. -/
def freeSheafMap (p : L.obj ⟶ M.obj) (hp : IsEquivariant p) :
    L.freeSheaf J R ⟶ M.freeSheaf J R :=
  (freeSheafFunctor (twistedTopology ρ J) R).map (presheafMap p hp)

@[simp]
theorem freeSheafMap_id (L : GlobalLift (P := P) (ρ := ρ)) :
    freeSheafMap J R (𝟙 L.obj) (isEquivariant_id L) = 𝟙 (L.freeSheaf J R) := by
  unfold freeSheafMap
  rw [presheafMap_id]
  exact (freeSheafFunctor (twistedTopology ρ J) R).map_id L.presheaf

theorem freeSheafMap_comp (p : L.obj ⟶ M.obj) (q : M.obj ⟶ N.obj)
    (hp : IsEquivariant p) (hq : IsEquivariant q) :
    freeSheafMap J R (p ≫ q) (hp.comp hq) =
      freeSheafMap J R p hp ≫ freeSheafMap J R q hq := by
  unfold freeSheafMap
  rw [presheafMap_comp p q hp hq, Functor.map_comp]
  rfl

/-- The fixed-section equivalence commutes with the induced free sheaf map. -/
theorem freeSheafHomEquivFixedSections_naturality_left_val
    (p : L.obj ⟶ M.obj) (hp : IsEquivariant p)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))
    (f : M.freeSheaf J R ⟶ F) :
    (L.freeSheafHomEquivFixedSections J R F (freeSheafMap J R p hp ≫ f)).val =
      F.obj.map ((ι P ρ).map p).op
        (M.freeSheafHomEquivFixedSections J R F f).val := by
  change (freeSheafFunctor (twistedTopology ρ J) R).obj M.presheaf ⟶ F at f
  change (L.homEquivFixedSections (F.obj ⋙ forget (ModuleCat.{w} R))
    ((freeSheafAdjunction (twistedTopology ρ J) R).homEquiv L.presheaf F
      ((freeSheafFunctor (twistedTopology ρ J) R).map (presheafMap p hp) ≫ f))).val =
      (F.obj ⋙ forget (ModuleCat.{w} R)).map ((ι P ρ).map p).op
        (M.homEquivFixedSections (F.obj ⋙ forget (ModuleCat.{w} R))
          ((freeSheafAdjunction (twistedTopology ρ J) R).homEquiv M.presheaf F f)).val
  rw [Adjunction.homEquiv_naturality_left]
  exact homEquivFixedSections_naturality_left_val p hp _ _

section Discrete

variable [TopologicalSpace G]
variable (S : LocalActionSystem (TwistedOver P ρ) G)
variable [S.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable (hS : S.IsLiftSystem)
variable (hL : L.EventuallyEquivariant S) (hM : M.EventuallyEquivariant S)

/-- The same free sheaf map in the actual discrete sheaf category. -/
def discreteFreeSheafMap (p : L.obj ⟶ M.obj) (hp : IsEquivariant p) :
    L.discreteFreeSheaf S J R hS hL ⟶ M.discreteFreeSheaf S J R hS hM :=
  ⟨freeSheafMap J R p hp⟩

@[simp]
theorem discreteFreeSheafMap_id (L : GlobalLift (P := P) (ρ := ρ))
    (hL : L.EventuallyEquivariant S) :
    discreteFreeSheafMap J R S hS hL hL (𝟙 L.obj) (isEquivariant_id L) =
      𝟙 (L.discreteFreeSheaf S J R hS hL) := by
  apply ObjectProperty.hom_ext
  exact freeSheafMap_id J R L

theorem discreteFreeSheafMap_comp (hN : N.EventuallyEquivariant S)
    (p : L.obj ⟶ M.obj) (q : M.obj ⟶ N.obj)
    (hp : IsEquivariant p) (hq : IsEquivariant q) :
    discreteFreeSheafMap J R S hS hL hN (p ≫ q) (hp.comp hq) =
      discreteFreeSheafMap J R S hS hL hM p hp ≫
        discreteFreeSheafMap J R S hS hM hN q hq := by
  apply ObjectProperty.hom_ext
  exact freeSheafMap_comp J R p q hp hq

/-- Precomposition in the discrete category gives precisely the same
restriction of the represented fixed section. -/
theorem discreteFreeSheafHomEquivFixedSections_naturality_left_val
    (p : L.obj ⟶ M.obj) (hp : IsEquivariant p)
    (F : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (f : M.discreteFreeSheaf S J R hS hM ⟶ F) :
    (L.discreteFreeSheafHomEquivFixedSections S J R hS hL F
      (discreteFreeSheafMap J R S hS hL hM p hp ≫ f)).val =
      F.obj.obj.map ((ι P ρ).map p).op
        (M.discreteFreeSheafHomEquivFixedSections S J R hS hM F f).val := by
  exact freeSheafHomEquivFixedSections_naturality_left_val J R p hp F.obj f.hom

end Discrete

variable [HasSheafify J (ModuleCat.{w} R)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The induced free sheaf map restricts to the actual ordinary free
representable map, through the already specified comparison isomorphisms. -/
theorem freeSheafMap_restriction
    (p : L.obj ⟶ M.obj) (hp : IsEquivariant p) :
    (L.freeSheafRestrictionIso J R).inv ≫
        (restriction ρ J (ModuleCat.{w} R)).map (freeSheafMap J R p hp) =
      (freeSheafFunctor J R).map (shrinkYoneda.{w}.map p) ≫
        (M.freeSheafRestrictionIso J R).inv := by
  apply (freeRepresentableHomEquiv J R L.obj
    ((restriction ρ J (ModuleCat.{w} R)).obj (M.freeSheaf J R))).injective
  rw [freeRepresentableHomEquiv_restriction,
    freeRepresentableHomEquiv_naturality_left]
  have h := freeSheafHomEquivFixedSections_naturality_left_val J R p hp
    (M.freeSheaf J R) (𝟙 (M.freeSheaf J R))
  rw [Category.comp_id] at h
  rw [h]
  have h' := M.freeRepresentableHomEquiv_restriction J R
    (M.freeSheaf J R) (𝟙 (M.freeSheaf J R))
  rw [(restriction ρ J (ModuleCat.{w} R)).map_id, Category.comp_id] at h'
  rw [h']
  rfl

end Sheaf

end Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift
