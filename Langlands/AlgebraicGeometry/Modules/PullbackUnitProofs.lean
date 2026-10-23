import Langlands.AlgebraicGeometry.Modules.PullbackUnitStatements

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
lemma pullbackUnitAdjunction : PullbackUnitAdjunctionStatement.{u} := by
  intro X Y f
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
lemma pullbackUnitIdentity : PullbackUnitIdentityStatement.{u} := by
  intro X
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [pullbackUnitAdjunction]
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom (SheafOfModules.unit X.ringCatSheaf)
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  rw [Adjunction.homEquiv_unit, ← h]
  change unitToPushforwardUnit (𝟙 X) =
    𝟙 (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)
  simp only [Category.id_comp]
  rfl

/-- Transport an adjunction hom-equivalence along conjugate transformations. -/
lemma homEquiv_conjugate {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {A : C} {B : D} (k : L₁.obj A ⟶ B) :
    adj₂.homEquiv _ _ (α.app A ≫ k) =
      adj₁.homEquiv _ _ k ≫ (conjugateEquiv adj₁ adj₂ α).app B := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← unit_conjugateEquiv]
  rw [Category.assoc, ← NatTrans.naturality, ← Category.assoc]

/-- Evaluate a composite adjunction on a composite involving a mapped morphism. -/
lemma homEquiv_comp_map {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {A : C} {B : D} {T : E} (k : L₁.obj A ⟶ B) (l : L₂.obj B ⟶ T) :
    (adj₁.comp adj₂).homEquiv _ _ (L₂.map k ≫ l) =
      adj₁.homEquiv _ _ k ≫ R₁.map (adj₂.homEquiv _ _ l) := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

set_option backward.isDefEq.respectTransparency false in
lemma pullbackUnitComposition : PullbackUnitCompositionStatement.{u} := by
  intro X Y Z f g
  have he := homEquiv_comp_map
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (pullbackUnitIso g).hom (pullbackUnitIso f).hom
  rw [pullbackUnitAdjunction, pullbackUnitAdjunction] at he
  have hc := homEquiv_conjugate
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv
    ((Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫
      (pullbackUnitIso f).hom)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, he] at hc
  apply ((Scheme.Modules.pullbackComp f g).app
    (SheafOfModules.unit Z.ringCatSheaf)).eq_inv_comp.mp
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [pullbackUnitAdjunction]
  exact hc.trans rfl |>.symm

lemma pullbackUnitCoherence : PullbackUnitCoherenceStatement.{u} :=
  ⟨pullbackUnitAdjunction, pullbackUnitIdentity, pullbackUnitComposition⟩

end Langlands.Scheme.Modules
