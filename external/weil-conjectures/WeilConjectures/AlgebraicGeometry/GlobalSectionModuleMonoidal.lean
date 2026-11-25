/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import WeilConjectures.AlgebraicGeometry.GlobalSectionModuleOplaxNormalized

/-! # Tensor structure of global scalar extension on module sheaves

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
algebra.tex, Tag 00DK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive
private noncomputable def bottomModuleEquivalence
    {D : Type u} [SmallCategory D]
    (R : Sheaf (⊥ : GrothendieckTopology D) RingCat.{u}) :
    SheafOfModules.{u} R ≌ PresheafOfModules.{u} R.obj where
  functor := SheafOfModules.forget R
  inverse :=
    { obj := fun N ↦ ⟨N, Presheaf.isSheaf_bot _⟩
      map := fun g ↦ ⟨g⟩ }
  unitIso := NatIso.ofComponents (fun _ ↦ { hom := ⟨𝟙 _⟩, inv := ⟨𝟙 _⟩ })
  counitIso := Iso.refl _

private noncomputable instance constantPreservesColimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (I : Type) [SmallCategory I] :
    PreservesColimitsOfShape I (ringFamilyConstantPresheaf O) where
  preservesColimit := by
    intro K
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ ?_)⟩
    let R := ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf.{u} (↑(ringFamilyGlobalRing O) : Type u)))
    let V : RingSiteModules (ringFamilyGlobalRing O) ⥤
        ModuleCat.{u} (ringFamilyGlobalRing O) :=
      SheafOfModules.forget.{u} R ⋙ PresheafOfModules.evaluation R.obj
        (op ⟨PUnit.unit⟩)
    haveI : (SheafOfModules.forget R).IsEquivalence :=
      (bottomModuleEquivalence R).isEquivalence_functor
    haveI : PreservesColimit K (SheafOfModules.forget.{u} R) := inferInstance
    haveI : PreservesColimit (K ⋙ SheafOfModules.forget.{u} R)
        (PresheafOfModules.evaluation R.obj (op ⟨PUnit.unit⟩)) := inferInstance
    haveI : PreservesColimit K V := by
      dsimp only [V]
      infer_instance
    change IsColimit (V.mapCocone c)
    exact isColimitOfPreserves V hc

/-- The actual global scalar extension preserves small colimits.
Source: Stacks Project, algebraization.tex, Tag 099E. Constant presheaves preserve
colimits by evaluation on the one-point bottom site; the other two functors are left
adjoints. (auxiliary; not a blueprint node). -/
theorem ringFamilyGlobalExtension_preservesColimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (I : Type) [SmallCategory I] :
    PreservesColimitsOfShape I (ringFamilyGlobalExtension O) := by
  have := constantPreservesColimits O I
  have := (PresheafOfModules.pullbackPushforwardAdjunction
    (ringFamilyGlobalEvaluation O)).isLeftAdjoint
  unfold ringFamilyGlobalExtension
  infer_instance

/-- Global-section scalar extension is strong monoidal with the prescribed multiplication
as its inverse unit constraint. This statement concerns module sheaves, without complexes
or localizations.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E.
(auxiliary; not a blueprint node).

Proof: evaluate module sheaves on the one-point bottom-topology site to obtain A-modules.
On each site object V the tensor constraint is
(b tensor x) tensor (c tensor y) to bc tensor (x tensor y), inverse
b tensor (x tensor y) to (b tensor x) tensor (1 tensor y). Balancing over A and over O(V)
makes both maps well-defined; their composites are identities on pure tensors, which
generate the respective modules. These maps commute with restriction, since evaluation
A to O(V) is a map of ring presheaves. They therefore give constraints for the composite
of constant presheaves and the chosen presheaf pullback, identifying that pullback with
sectionwise extension by uniqueness of left adjoints to restriction of scalars. Compose
with the strong monoidal module sheafification functor. Associativity sends any triple
tensor to the product of its three scalar coefficients; the two unit identities are
multiplication by one, so the constraints are coherent. The inverse unit comparison is
multiplication O tensor_A A to O; its transpose through the two adjunctions is evaluation
of a global section. Hence it equals ringFamilyGlobalExtensionUnit as defined, rather
than an unspecified unit isomorphism. The argument includes empty sites and zero rings. -/
theorem ringFamilyGlobalExtension_module_monoidal
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.monoidalCategory
      (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
    ∃ mon : (ringFamilyGlobalExtension O).Monoidal,
      letI := mon
      Functor.OplaxMonoidal.η (ringFamilyGlobalExtension O) =
        ringFamilyGlobalExtensionUnit O := by
  letI : MonoidalCategory (SheafOfModules ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj O)) := SheafOfModules.monoidalCategory O
  letI : MonoidalCategory (RingSiteModules (ringFamilyGlobalRing O)) :=
    SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
  obtain ⟨oplax, hη, hδ, hunit⟩ := ringFamilyGlobalExtension_oplax_normalized O
  letI := oplax
  letI : IsIso (Functor.OplaxMonoidal.η (ringFamilyGlobalExtension O)) := hη
  letI : ∀ M N, IsIso (Functor.OplaxMonoidal.δ (ringFamilyGlobalExtension O) M N) := hδ
  refine ⟨Functor.Monoidal.ofOplaxMonoidal (ringFamilyGlobalExtension O), ?_⟩
  exact hunit

end CategoryTheory
