import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupTransportCovering
import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupInvariantSections
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.RepresentationTheory.Rep.Res

/-! # Local section representations on the finite rational transport site -/

noncomputable section

universe u v uA vA uR uM uJ vJ

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- The inverse subgroup label induces the forward operator on contravariant sections. -/
def operator (X : ρ.OpenSubgroupTransport) (k : X.subgroup) : X ⟶ X where
  label := (k : G)⁻¹
  subgroup_le := by
    intro h hh
    rw [mem_conjugateOpenSubgroup] at hh
    have ht := X.subgroup.mul_mem
      (X.subgroup.mul_mem (X.subgroup.inv_mem k.property) hh) k.property
    simpa [mul_assoc] using ht
  mapsTo := by
    intro x hx
    have hk := X.domain.property (X.subgroup.inv_mem k.property)
    rw [mem_locusOpenSubgroup] at hk
    rw [← hk]
    exact ⟨x, hx, rfl⟩

@[simp] theorem operator_label (X : ρ.OpenSubgroupTransport) (k : X.subgroup) :
    (X.operator k).label = (k : G)⁻¹ := rfl

@[simp] theorem operator_one (X : ρ.OpenSubgroupTransport) :
    X.operator 1 = 𝟙 X :=
  Hom.ext (inv_one : (1 : G)⁻¹ = 1)

theorem operator_mul (X : ρ.OpenSubgroupTransport) (k l : X.subgroup) :
    X.operator (k * l) = X.operator k ≫ X.operator l :=
  Hom.ext (mul_inv_rev (k : G) (l : G))

/-- No labels are discarded in constructing these actual transport isomorphisms. -/
def operatorIso (X : ρ.OpenSubgroupTransport) (k : X.subgroup) : X ≅ X where
  hom := X.operator k
  inv := X.operator k⁻¹
  hom_inv_id := by rw [← operator_mul, mul_inv_cancel, operator_one]
  inv_hom_id := by rw [← operator_mul, inv_mul_cancel, operator_one]

/-- Every original arrow intertwines the local operators by its actual conjugation map. -/
theorem operator_comm {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (k : X.subgroup) :
    X.operator k ≫ f = f ≫ Y.operator (f.groupHom k) := by
  apply Hom.ext
  simp [mul_assoc]

/-- On the actual quotient-algebra presheaf these are the published forward operators. -/
theorem operator_restriction (X : ρ.OpenSubgroupTransport) (k : X.subgroup) :
    (X.operator k).restriction = X.sectionOperator k := by
  apply X.domain.obj.hom_ext
  rw [Hom.restriction_comp_baseMap]
  change X.domain.obj.baseMap.comp (ρ.toMonoidHom (k : G)⁻¹).inv =
    (ρ.sectionAction X.domain.obj
      (ρ.invariantStabilizerInclusion X.subgroup X.domain k)).hom.comp
        X.domain.obj.baseMap
  rw [ρ.sectionAction_comp_baseMap, map_inv]
  rfl

variable (A : Type uA) [Category.{vA} A]

/-- Evaluation of any actual transport presheaf with its chosen subgroup action. -/
def presheafSectionAction (X : ρ.OpenSubgroupTransport) :
    ((ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A) ⥤ Action A X.subgroup where
  obj F :=
    { V := F.obj (op X)
      ρ :=
        { toFun k := F.map (X.operator k).op
          map_one' := by rw [operator_one, op_id, F.map_id]; rfl
          map_mul' k l := by rw [operator_mul, op_comp, F.map_comp]; rfl } }
  map f :=
    { hom := f.app (op X)
      comm k := f.naturality (X.operator k).op }

@[simp] theorem presheafSectionAction_obj_ρ (X : ρ.OpenSubgroupTransport)
    (F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A) (k : X.subgroup) :
    ((presheafSectionAction A X).obj F).ρ k = F.map (X.operator k).op := rfl

/-- The original presheaf map, as an intertwiner after conjugation of subgroups. -/
def presheafSectionRestriction {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    presheafSectionAction A Y ⋙ Action.res A f.groupHom.toMonoidHom ⟶
      presheafSectionAction A X where
  app F :=
    { hom := F.map f.op
      comm k := by
        change F.map (Y.operator (f.groupHom k)).op ≫ F.map f.op =
          F.map f.op ≫ F.map (X.operator k).op
        rw [← F.map_comp, ← F.map_comp]
        exact congrArg (fun q => F.map q.op) (operator_comm f k).symm }
  naturality {F E} a := by
    apply Action.Hom.ext
    exact (a.naturality f.op).symm

@[simp] theorem presheafSectionRestriction_app_hom
    {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A) :
    ((presheafSectionRestriction A f).app F).hom = F.map f.op := rfl

@[simp] theorem presheafSectionRestriction_id_hom (X : ρ.OpenSubgroupTransport)
    (F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A) :
    ((presheafSectionRestriction A (𝟙 X)).app F).hom = 𝟙 (F.obj (op X)) := by
  simp

theorem presheafSectionRestriction_comp_hom {X Y Z : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ A) :
    ((presheafSectionRestriction A (f ≫ g)).app F).hom =
      ((presheafSectionRestriction A g).app F).hom ≫
        ((presheafSectionRestriction A f).app F).hom := by
  simp only [presheafSectionRestriction_app_hom, op_comp, F.map_comp]

/-- Categorical sheaves on the existing finite point-image covering topology. -/
abbrev TransportSheaf :=
  CategoryTheory.Sheaf (finiteTopology ρ) A

/-- Actual evaluation, with no change of the sheaf's section object. -/
abbrev evaluation (X : ρ.OpenSubgroupTransport) : TransportSheaf (ρ := ρ) A ⥤ A :=
  (sheafSections (finiteTopology ρ) A).obj (op X)

/-- The local subgroup acts on all sections of an actual transport sheaf. -/
def sectionAction (X : ρ.OpenSubgroupTransport) :
    TransportSheaf (ρ := ρ) A ⥤ Action A X.subgroup :=
  sheafToPresheaf (finiteTopology ρ) A ⋙ presheafSectionAction A X

/-- Forgetting the local action is exactly ordinary sheaf evaluation. -/
def sectionActionForgetIso (X : ρ.OpenSubgroupTransport) :
    sectionAction A X ⋙ Action.forget A X.subgroup ≅ evaluation A X :=
  Iso.refl _

/-- Restriction along every original arrow is natural in the actual sheaf. -/
def sectionRestriction {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    sectionAction A Y ⋙ Action.res A f.groupHom.toMonoidHom ⟶ sectionAction A X :=
  Functor.whiskerLeft (sheafToPresheaf (finiteTopology ρ) A)
    (presheafSectionRestriction A f)

@[simp] theorem sectionRestriction_app_hom
    {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (F : TransportSheaf (ρ := ρ) A) :
    ((sectionRestriction A f).app F).hom = F.obj.map f.op := rfl

instance evaluation_preservesLimitsOfShape
    (J : Type uJ) [Category.{vJ} J] [HasLimitsOfShape J A]
    (X : ρ.OpenSubgroupTransport) :
    PreservesLimitsOfShape J (evaluation A X) :=
  inferInstanceAs (PreservesLimitsOfShape J
    (sheafToPresheaf (finiteTopology ρ) A ⋙
      (CategoryTheory.evaluation _ _).obj (op X)))

instance evaluation_preservesFiniteLimits [HasFiniteLimits A]
    (X : ρ.OpenSubgroupTransport) :
    PreservesFiniteLimits (evaluation A X) := ⟨fun _ _ _ => inferInstance⟩

variable (R : Type uR) [CommRing R]

/-- Module-valued categorical sheaves on this finite rational transport site. -/
abbrev ModuleSheaf := TransportSheaf (ρ := ρ) (ModuleCat.{uM} R)

/-- The complete section module with its algebraic representation of the object's subgroup. -/
def sectionRepresentation (X : ρ.OpenSubgroupTransport) :
    ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R ⥤ Rep.{uM} R X.subgroup :=
  sectionAction (ModuleCat.{uM} R) X ⋙ Rep.ActionToRep R X.subgroup

@[simp] theorem sectionRepresentation_obj_ρ (X : ρ.OpenSubgroupTransport)
    (F : ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R) (k : X.subgroup) :
    ((sectionRepresentation R X).obj F).ρ k =
      (F.obj.map (X.operator k).op).hom := rfl

instance sectionRepresentation_additive (X : ρ.OpenSubgroupTransport) :
    (sectionRepresentation R X :
      ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R ⥤ _).Additive where
  map_add {F E} f g := by ext s; rfl

/-- Forgetting the representation retains every actual local section. -/
def sectionRepresentationForgetIso (X : ρ.OpenSubgroupTransport) :
    sectionRepresentation R X ⋙ forget₂ (Rep.{uM} R X.subgroup) (ModuleCat.{uM} R) ≅
      evaluation (ModuleCat.{uM} R) X :=
  Iso.refl _

instance sectionRepresentation_preservesFiniteLimits (X : ρ.OpenSubgroupTransport) :
    PreservesFiniteLimits (sectionRepresentation R X :
      ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R ⥤ _) := by
  have : PreservesFiniteLimits
      (sectionRepresentation R X ⋙
        forget₂ (Rep.{uM} R X.subgroup) (ModuleCat.{uM} R)) :=
    preservesFiniteLimits_of_natIso (sectionRepresentationForgetIso R X).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (Rep.{uM} R X.subgroup) (ModuleCat.{uM} R))

/-- Each original labelled arrow gives its actual section map as a module intertwiner. -/
def representationRestriction {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    sectionRepresentation R Y ⋙ Rep.resFunctor f.groupHom.toMonoidHom ⟶
      (sectionRepresentation R X : ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R ⥤ _) where
  app F := Rep.ofHom
    { toLinearMap := (F.obj.map f.op).hom
      isIntertwining' k := by
        exact congrArg ModuleCat.Hom.hom
          (((sectionRestriction (ModuleCat.{uM} R) f).app F).comm k) }
  naturality {F E} a := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact congrArg ModuleCat.Hom.hom (a.hom.naturality f.op).symm

@[simp] theorem representationRestriction_app_hom
    {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (F : ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R) :
    ((representationRestriction R f).app F).hom.toLinearMap =
      (F.obj.map f.op).hom := rfl

@[simp] theorem representationRestriction_id_hom (X : ρ.OpenSubgroupTransport)
    (F : ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R) :
    ((representationRestriction R (𝟙 X)).app F).hom.toLinearMap =
      LinearMap.id := by
  simp only [representationRestriction_app_hom, op_id, F.obj.map_id]
  rfl

/-- Composition retains the actual contravariant module restrictions. -/
theorem representationRestriction_comp_hom {X Y Z : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : ModuleSheaf.{u, v, uR, uM} (ρ := ρ) R) :
    ((representationRestriction R (f ≫ g)).app F).hom.toLinearMap =
      (((representationRestriction R f).app F).hom.toLinearMap).comp
        ((representationRestriction R g).app F).hom.toLinearMap := by
  simp only [representationRestriction_app_hom, op_comp, F.obj.map_comp]
  rfl

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
