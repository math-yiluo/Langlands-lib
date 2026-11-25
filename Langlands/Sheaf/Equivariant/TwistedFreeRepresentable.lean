import Langlands.Sheaf.Equivariant.TwistedOver
import Langlands.Cohomology.SiteCech.FreeSections

/-! # Free representables attached to globally lifted objects -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology.SiteCech

universe u v z w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type z} [Group G] {ρ : G →* Aut X}

/-- An object over the base with a lift of the entire acting group.
The inverse twist convention makes restriction on sections a left action. -/
structure GlobalLift where
  obj : P.Over ⊤ X
  action : G →* (End ((ι P ρ).obj obj))ᵐᵒᵖ
  twist : ∀ g, Hom.twist (action g).unop.asHom = g⁻¹

namespace GlobalLift

variable (L : GlobalLift (P := P) (ρ := ρ))

theorem action_mul_left (g h : G) :
    Hom.left (L.action (g * h)).unop.asHom =
      Hom.left (L.action g).unop.asHom ≫ Hom.left (L.action h).unop.asHom := by
  rw [map_mul, MulOpposite.unop_mul]
  rfl

/-- Precompose a plain map by a twisted map and cancel its twist using the
global lift on the represented object. -/
def precomp {V W : TwistedOver P ρ} (f : V ⟶ W) (k : W.obj ⟶ L.obj) :
    V.obj ⟶ L.obj :=
  MorphismProperty.Over.homMk
    (Hom.left f ≫ k.left ≫ Hom.left (L.action (Hom.twist f)).unop.asHom) (by
      have h := Hom.w (f ≫ (ι P ρ).map k ≫ (L.action (Hom.twist f)).unop.asHom)
      simpa only [comp_left, homMk_left, comp_twist, homMk_twist, L.twist,
        mul_one, inv_mul_cancel,
        rho_one_hom, Category.comp_id] using h)

@[simp]
theorem precomp_left {V W : TwistedOver P ρ} (f : V ⟶ W) (k : W.obj ⟶ L.obj) :
    (L.precomp f k).left =
      Hom.left f ≫ k.left ≫ Hom.left (L.action (Hom.twist f)).unop.asHom := rfl

@[simp]
theorem precomp_plain {V W : P.Over ⊤ X} (f : V ⟶ W) (k : W ⟶ L.obj) :
    L.precomp ((ι P ρ).map f) k = f ≫ k := by
  apply MorphismProperty.Over.Hom.ext
  simp only [precomp_left, homMk_left, homMk_twist, map_one, MulOpposite.unop_one]
  change f.left ≫ k.left ≫ 𝟙 L.obj.left = f.left ≫ k.left
  rw [Category.comp_id]

@[simp]
theorem precomp_id (V : TwistedOver P ρ) (k : V.obj ⟶ L.obj) :
    L.precomp (𝟙 V) k = k := by
  apply MorphismProperty.Over.Hom.ext
  simp only [precomp_left, id_left, id_twist, map_one, MulOpposite.unop_one]
  change (𝟙 _) ≫ k.left ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

theorem precomp_comp {V W Z : TwistedOver P ρ} (f : V ⟶ W) (g : W ⟶ Z)
    (k : Z.obj ⟶ L.obj) :
    L.precomp (f ≫ g) k = L.precomp f (L.precomp g k) := by
  apply MorphismProperty.Over.Hom.ext
  change (Hom.left f ≫ Hom.left g) ≫ k.left ≫
      Hom.left (L.action (Hom.twist g * Hom.twist f)).unop.asHom =
    Hom.left f ≫ (Hom.left g ≫ k.left ≫ Hom.left (L.action (Hom.twist g)).unop.asHom) ≫
      Hom.left (L.action (Hom.twist f)).unop.asHom
  rw [L.action_mul_left]
  simp only [Category.assoc]

@[simp]
theorem precomp_action (g : G) :
    L.precomp (L.action g).unop.asHom (𝟙 L.obj) = 𝟙 L.obj := by
  apply MorphismProperty.Over.Hom.ext
  change Hom.left (L.action g).unop.asHom ≫ 𝟙 _ ≫
    Hom.left (L.action (Hom.twist (L.action g).unop.asHom)).unop.asHom = 𝟙 _
  rw [L.twist, Category.id_comp, ← action_mul_left, mul_inv_cancel, map_one]
  rfl

theorem ι_precomp {V W : TwistedOver P ρ} (f : V ⟶ W) (k : W.obj ⟶ L.obj) :
    (ι P ρ).map (L.precomp f k) =
      f ≫ (ι P ρ).map k ≫ (L.action (Hom.twist f)).unop.asHom := by
  apply hom_ext
  · simp only [homMk_twist, comp_twist, L.twist, mul_one, inv_mul_cancel]
  · rfl

variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- The equivariant representable of a globally lifted object. Its values are
the ordinary representable; twisted restrictions cancel the twist on the target. -/
def presheaf : (TwistedOver P ρ)ᵒᵖ ⥤ Type w where
  obj V := Shrink (V.unop.obj ⟶ L.obj)
  map f := ↾fun k =>
    equivShrink _ (L.precomp f.unop ((equivShrink _).symm k))
  map_id V := by
    apply ConcreteCategory.ext_apply
    intro k
    change equivShrink _ (L.precomp (𝟙 V.unop) ((equivShrink _).symm k)) = k
    rw [precomp_id, Equiv.apply_symm_apply]
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    intro k
    change equivShrink _ (L.precomp (g.unop ≫ f.unop) ((equivShrink _).symm k)) =
      equivShrink _ (L.precomp g.unop ((equivShrink _).symm
        (equivShrink _ (L.precomp f.unop ((equivShrink _).symm k)))))
    rw [Equiv.symm_apply_apply, precomp_comp]

/-- Forgetting the equivariant structure recovers the actual small ordinary
representable presheaf. -/
def restrictionIso : (ι P ρ).op ⋙ L.presheaf ≅ shrinkYoneda.{w}.obj L.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro V W f
    apply ConcreteCategory.ext_apply
    intro k
    change equivShrink _ (L.precomp ((ι P ρ).map f.unop)
      ((equivShrink _).symm k)) = equivShrink _ (f.unop ≫ (equivShrink _).symm k)
    rw [precomp_plain])

/-- Sections fixed by the entire specified lift. -/
abbrev FixedSections (F : (TwistedOver P ρ)ᵒᵖ ⥤ Type w) : Type w :=
  {s : F.obj (op ((ι P ρ).obj L.obj)) //
    ∀ g : G, F.map (L.action g).unop.asHom.op s = s}

/-- A fixed section extends uniquely along ordinary maps to a map from the
lifted representable. -/
def fixedSectionMap (F : (TwistedOver P ρ)ᵒᵖ ⥤ Type w) (s : L.FixedSections F) :
    L.presheaf ⟶ F where
  app V := ↾fun k => F.map ((ι P ρ).map ((equivShrink _).symm k)).op s.val
  naturality V W f := by
    apply ConcreteCategory.ext_apply
    intro k
    change F.map ((ι P ρ).map ((equivShrink _).symm
      (equivShrink _ (L.precomp f.unop ((equivShrink _).symm k))))).op s.val =
        F.map f (F.map ((ι P ρ).map ((equivShrink _).symm k)).op s.val)
    rw [Equiv.symm_apply_apply, L.ι_precomp]
    simp only [op_comp, Functor.map_comp, types_comp_apply, s.property,
      Quiver.Hom.op_unop]

/-- Evaluation of a map from the lifted representable at its identity generator
is fixed by the lift. -/
def fixedSectionOfMap (F : (TwistedOver P ρ)ᵒᵖ ⥤ Type w) (α : L.presheaf ⟶ F) :
    L.FixedSections F :=
  ⟨α.app (op ((ι P ρ).obj L.obj)) (equivShrink _ (𝟙 L.obj)), by
    intro g
    have h := ConcreteCategory.congr_hom (α.naturality (L.action g).unop.asHom.op)
      (equivShrink _ (𝟙 L.obj))
    change α.app _ (equivShrink _ (L.precomp (L.action g).unop.asHom
      ((equivShrink _).symm (equivShrink _ (𝟙 L.obj))))) =
        F.map (L.action g).unop.asHom.op
          (α.app (op ((ι P ρ).obj L.obj)) (equivShrink _ (𝟙 L.obj))) at h
    rw [Equiv.symm_apply_apply, precomp_action] at h
    exact h.symm⟩

/-- The lifted representable represents precisely the sections fixed by its
global lift. -/
def homEquivFixedSections (F : (TwistedOver P ρ)ᵒᵖ ⥤ Type w) :
    (L.presheaf ⟶ F) ≃ L.FixedSections F where
  toFun := L.fixedSectionOfMap F
  invFun := L.fixedSectionMap F
  left_inv α := by
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.ext_apply
    intro k
    change Shrink.{w} (V.unop.obj ⟶ L.obj) at k
    have h := ConcreteCategory.congr_hom
      (α.naturality ((ι P ρ).map ((equivShrink _).symm k)).op)
        (equivShrink _ (𝟙 L.obj))
    change α.app V (equivShrink _ (L.precomp
      ((ι P ρ).map ((equivShrink _).symm k))
        ((equivShrink _).symm (equivShrink _ (𝟙 L.obj))))) =
      F.map ((ι P ρ).map ((equivShrink _).symm k)).op
        (α.app (op ((ι P ρ).obj L.obj)) (equivShrink _ (𝟙 L.obj))) at h
    rw [Equiv.symm_apply_apply,
      L.precomp_plain ((equivShrink _).symm k) (𝟙 L.obj),
      Category.comp_id, Equiv.apply_symm_apply] at h
    exact h.symm
  right_inv s := by
    apply Subtype.ext
    change F.map ((ι P ρ).map
      ((equivShrink _).symm (equivShrink _ (𝟙 L.obj)))).op s.val = s.val
    rw [Equiv.symm_apply_apply]
    change F.map (𝟙 (op ((ι P ρ).obj L.obj))) s.val = s.val
    rw [F.map_id]
    rfl

section Sheaf

variable [P.RespectsIso]
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- The equivariant module sheaf freely generated by the lifted representable. -/
def freeSheaf : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) :=
  (freeSheafFunctor (twistedTopology ρ J) R).obj L.presheaf

/-- Morphisms from the free lifted sheaf correspond to sections fixed by the
specified global lift. -/
def freeSheafHomEquivFixedSections (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :
    (L.freeSheaf J R ⟶ F) ≃ L.FixedSections (F.obj ⋙ forget (ModuleCat.{w} R)) :=
  ((freeSheafAdjunction (twistedTopology ρ J) R).homEquiv L.presheaf F).trans
    (L.homEquivFixedSections _)

theorem freeSheafHomEquivFixedSections_val
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) (f : L.freeSheaf J R ⟶ F) :
    (L.freeSheafHomEquivFixedSections J R F f).val =
      f.hom.app (op ((ι P ρ).obj L.obj))
        ((toSheafify (twistedTopology ρ J) (L.presheaf ⋙ ModuleCat.free R)).app
          (op ((ι P ρ).obj L.obj)) (ModuleCat.freeMk (equivShrink _ (𝟙 L.obj)))) := rfl

variable [HasSheafify J (ModuleCat.{w} R)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- Ordinary restriction of the free lifted sheaf is the actual ordinary free
representable sheaf. -/
def freeSheafRestrictionIso :
    (restriction ρ J (ModuleCat.{w} R)).obj (L.freeSheaf J R) ≅
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj L.obj) :=
  (((ι P ρ).pushforwardContinuousSheafificationCompatibility (ModuleCat.{w} R)
    J (twistedTopology ρ J)).app (L.presheaf ⋙ ModuleCat.free R)).symm ≪≫
      (presheafToSheaf J (ModuleCat.{w} R)).mapIso
        (Functor.isoWhiskerRight L.restrictionIso (ModuleCat.free R))

/-- The ordinary comparison identifies the two sheafified generators. -/
theorem freeSheafRestrictionIso_inv_unit :
    toSheafify J (shrinkYoneda.{w}.obj L.obj ⋙ ModuleCat.free R) ≫
        (L.freeSheafRestrictionIso J R).inv.hom =
      Functor.whiskerRight L.restrictionIso.inv (ModuleCat.free R) ≫
        Functor.whiskerLeft (ι P ρ).op
          (toSheafify (twistedTopology ρ J) (L.presheaf ⋙ ModuleCat.free R)) := by
  change toSheafify J _ ≫
    (sheafifyMap J (Functor.whiskerRight L.restrictionIso.inv (ModuleCat.free R)) ≫
      (((ι P ρ).pushforwardContinuousSheafificationCompatibility (ModuleCat.{w} R)
        J (twistedTopology ρ J)).hom.app (L.presheaf ⋙ ModuleCat.free R)).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  congr 1
  exact (ι P ρ).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{w} R) J (twistedTopology ρ J) (L.presheaf ⋙ ModuleCat.free R)

/-- Under ordinary restriction, the represented section is exactly the section
specified by the fixed-section equivalence. -/
theorem freeRepresentableHomEquiv_restriction
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) (f : L.freeSheaf J R ⟶ F) :
    freeRepresentableHomEquiv J R L.obj ((restriction ρ J (ModuleCat.{w} R)).obj F)
      ((L.freeSheafRestrictionIso J R).inv ≫
        (restriction ρ J (ModuleCat.{w} R)).map f) =
      (L.freeSheafHomEquivFixedSections J R F f).val := by
  rw [freeRepresentableHomEquiv_apply, freeSheafHomEquivFixedSections_val]
  change f.hom.app _
    ((L.freeSheafRestrictionIso J R).inv.hom.app (op L.obj)
      ((toSheafify J (shrinkYoneda.{w}.obj L.obj ⋙ ModuleCat.free R)).app (op L.obj)
        (ModuleCat.freeMk (equivShrink _ (𝟙 L.obj))))) = _
  congr 1
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (L.freeSheafRestrictionIso_inv_unit J R) (op L.obj))
      (ModuleCat.freeMk (equivShrink _ (𝟙 L.obj)))
  change (L.freeSheafRestrictionIso J R).inv.hom.app (op L.obj)
    ((toSheafify J (shrinkYoneda.{w}.obj L.obj ⋙ ModuleCat.free R)).app (op L.obj)
      (ModuleCat.freeMk (equivShrink _ (𝟙 L.obj)))) =
    (toSheafify (twistedTopology ρ J) (L.presheaf ⋙ ModuleCat.free R)).app
      (op ((ι P ρ).obj L.obj)) ((ModuleCat.free R).map (𝟙 _)
        (ModuleCat.freeMk (equivShrink _ (𝟙 L.obj)))) at h
  rw [(ModuleCat.free R).map_id] at h
  exact h

end Sheaf

end GlobalLift

end Langlands.Sheaf.Equivariant.TwistedOver
