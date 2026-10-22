import Langlands.AlgebraicGeometry.RelativeDifferentialsMapsStatement

/-! # Coherence of the induced relative differential maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

variable {X Y Z S : AlgebraicGeometry.Scheme.{u}}

private lemma homEquiv_conjugate {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {A : C} {B : D} (f : L₁.obj A ⟶ B) :
    adj₂.homEquiv A B (α.app A ≫ f) =
      adj₁.homEquiv A B f ≫ (conjugateEquiv adj₁ adj₂ α).app B := by
  calc
    _ = (adj₁.unit.app A ≫ (conjugateEquiv adj₁ adj₂ α).app _) ≫ R₂.map f := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
        unit_conjugateEquiv]
    _ = _ := by
      rw [Adjunction.homEquiv_unit, Category.assoc, ← NatTrans.naturality,
        ← Category.assoc]

private lemma pullbackHomEquiv_id (M : X.Modules) :
    (pullbackPushforwardAdjunction (𝟙 X)).homEquiv M M ((pullbackId X).hom.app M) =
      (pushforwardId X).inv.app M := by
  have h := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))
    (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  change (𝟙 M) ≫ (pushforwardId X).inv.app M =
    (pullbackPushforwardAdjunction (𝟙 X)).homEquiv M M ((pullbackId X).hom.app M) at h
  simpa only [Category.id_comp] using h.symm

private lemma pullbackHomEquiv_comp (g : X ⟶ Y) (h : Y ⟶ Z)
    (A : Z.Modules) (B : Y.Modules) (M : X.Modules)
    (α : (pullback h).obj A ⟶ B) (β : (pullback g).obj B ⟶ M) :
    (pullbackPushforwardAdjunction (g ≫ h)).homEquiv A M
      ((pullbackComp g h).inv.app A ≫ (pullback g).map α ≫ β) =
        (pullbackPushforwardAdjunction h).homEquiv A B α ≫
          (pushforward h).map ((pullbackPushforwardAdjunction g).homEquiv B M β) ≫
            (pushforwardComp g h).hom.app M := by
  rw [homEquiv_conjugate
    ((pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ h)) (pullbackComp g h).inv]
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
  change (pullbackPushforwardAdjunction h).homEquiv _ _
    ((pullbackPushforwardAdjunction g).homEquiv _ _ ((pullback g).map α ≫ β)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Category.assoc]

lemma relativeDifferentialsPushforwardMap_id (f : X ⟶ S) :
    relativeDifferentialsPushforwardMap (𝟙 X) (Category.id_comp f) ≫
        (pushforwardId X).hom.app (relativeDifferentials f) =
      𝟙 (relativeDifferentials f) := by
  apply relativeDifferentials_hom_ext f
  rw [RelativeDerivation.postcomp_comp, relativeDifferentialsPushforwardMap_fac,
    RelativeDerivation.precompOver_id, RelativeDerivation.postcomp_id]

@[simp]
lemma relativeDifferentialsMap_id (f : X ⟶ S) :
    relativeDifferentialsMap (𝟙 X) (Category.id_comp f) =
      (pullbackId X).hom.app (relativeDifferentials f) := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [relativeDifferentialsMap_adjoint, pullbackHomEquiv_id]
  apply (cancel_mono ((pushforwardId X).hom.app (relativeDifferentials f))).1
  rw [relativeDifferentialsPushforwardMap_id]
  simp

lemma relativeDifferentialsPushforwardMap_comp (g : X ⟶ Y) (h : Y ⟶ Z)
    {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX) (wh : h ≫ fZ = fY) :
    relativeDifferentialsPushforwardMap h wh ≫
        (pushforward h).map (relativeDifferentialsPushforwardMap g wg) ≫
        (pushforwardComp g h).hom.app (relativeDifferentials fX) =
      relativeDifferentialsPushforwardMap (g ≫ h) (by rw [Category.assoc, wh, wg]) := by
  apply relativeDifferentials_hom_ext fZ
  rw [← Category.assoc, RelativeDerivation.postcomp_comp,
    RelativeDerivation.postcomp_comp, relativeDifferentialsPushforwardMap_fac,
    ← RelativeDerivation.precompOver_postcomp, relativeDifferentialsPushforwardMap_fac,
    RelativeDerivation.precompOver_comp, relativeDifferentialsPushforwardMap_fac]

/-- Composition compatibility with the actual pullback composition isomorphism. -/
lemma relativeDifferentialsMap_comp (g : X ⟶ Y) (h : Y ⟶ Z)
    {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX) (wh : h ≫ fZ = fY) :
    (pullbackComp g h).inv.app (relativeDifferentials fZ) ≫
        (pullback g).map (relativeDifferentialsMap h wh) ≫
        relativeDifferentialsMap g wg =
      relativeDifferentialsMap (g ≫ h) (by rw [Category.assoc, wh, wg]) := by
  apply ((pullbackPushforwardAdjunction (g ≫ h)).homEquiv _ _).injective
  rw [pullbackHomEquiv_comp, relativeDifferentialsMap_adjoint,
    relativeDifferentialsMap_adjoint, relativeDifferentialsMap_adjoint,
    relativeDifferentialsPushforwardMap_comp]

theorem relativeDifferentialsMapLaws : RelativeDifferentialsMapLawsStatement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y S g fX fY w α
    constructor
    · exact relativeDifferentialsMap_unique g w α
    · intro h
      subst α
      exact relativeDifferentialsMap_fac g w
  · intro X S f
    exact relativeDifferentialsMap_id f
  · intro X Y Z S g h fX fY fZ wg wh
    exact relativeDifferentialsMap_comp g h wg wh

end Langlands.Scheme
