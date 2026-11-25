/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact scalar localization of module sheaves

Source: Stacks Project, Modules on Sites, Tag 03ET, with Tags 03ER, 03ES,
03DA and 03DB, and Algebra, Tag 00HT.
(blueprint: lem-weil-pbc-scalar-localization-sheaf-exact)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open MonoidalCategory

section Helpers

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C} [HasSheafify J CommRingCat.{u}]
  (R : Sheaf J CommRingCat.{u})

omit [EssentiallySmall.{u} C] [HasSheafify J CommRingCat.{u}] in
private theorem tensor_presheaf_flat
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hP : ∀ U, Module.Flat (R.obj.obj U) (P.obj U)) :
    PreservesFiniteLimits (tensorRight P) := by
  constructor
  intro K _ _
  have (U : Cᵒᵖ) : Module.Flat (R.obj.obj U) (P.obj U) := hP U
  exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
    (fun U ↦ isLimitOfPreserves
      (tensorRight (show ModuleCat (R.obj.obj U) from P.obj U))
      (isLimitOfPreserves (PresheafOfModules.evaluation _ U) hc))⟩⟩⟩

omit [HasSheafify J CommRingCat.{u}] in
private theorem tensor_sheafification_flat
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hP : PreservesFiniteLimits (tensorRight P)) :
    PreservesFiniteLimits (tensorRight (C := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      ((PresheafOfModules.sheafification.{u} (R :=
        (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)).obj P)) := by
  let A := PresheafOfModules.sheafification.{u} (R :=
    (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (R :=
    (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)
  let I := SheafOfModules.forget.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
  let T := tensorRight (A.obj P)
  have : PreservesFiniteLimits (tensorRight P) := hP
  have : PreservesFiniteLimits I :=
    adj.rightAdjoint_preservesLimits.{u, u}.preservesFiniteLimits
  have : PreservesFiniteLimits A := inferInstanceAs
    (PreservesFiniteLimits (PresheafOfModules.sheafification.{u}
      (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)))
  have hpA : PreservesFiniteLimits (tensorRight P ⋙ A) :=
    comp_preservesFiniteLimits _ _
  let e : A ⋙ T ≅ tensorRight P ⋙ A := Functor.Monoidal.commTensorRight A P
  have : PreservesFiniteLimits (A ⋙ T) :=
    preservesFiniteLimits_of_natIso (F := tensorRight P ⋙ A) e.symm
  have : PreservesFiniteLimits (I ⋙ A ⋙ T) := comp_preservesFiniteLimits I (A ⋙ T)
  have : PreservesFiniteLimits ((I ⋙ A) ⋙ T) :=
    inferInstanceAs (PreservesFiniteLimits (I ⋙ A ⋙ T))
  exact preservesFiniteLimits_of_natIso
    (F := I ⋙ A ⋙ T) (Functor.isoWhiskerRight (asIso adj.counit) T)

private theorem localization_tensor_flat
    (s : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    PreservesFiniteLimits (tensorLeft (C := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
          (ringedLocalizationRingUnitOfUniverses.{u, uC, vC} R s))).obj
        (SheafOfModules.unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ringedLocalizationRingOfUniverses.{u, uC, vC} R s))))) := by
  let P := ringedSectionLocalizationPresheafOfUniverses.{u, uC, vC} R s
  have hp : PreservesFiniteLimits (tensorRight P) := tensor_presheaf_flat R P (by
    intro U
    exact IsLocalization.flat (ringedSectionLocalizationCarrierOfUniverses.{u, uC, vC} R s U)
      (Submonoid.powers (s.val U)))
  have : PreservesFiniteLimits (tensorRight
      (ringedSectionLocalizationOfUniverses R s)) := tensor_sheafification_flat R P hp
  obtain ⟨e, _⟩ := ringedLocalizationRing_moduleComparisonOfUniverses.{u, uC, vC} R s
  let L := (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
      (ringedLocalizationRingUnitOfUniverses.{u, uC, vC} R s))).obj
    (SheafOfModules.unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ringedLocalizationRingOfUniverses.{u, uC, vC} R s)))
  have : PreservesFiniteLimits (tensorRight L) := by
    exact preservesFiniteLimits_of_natIso ((curriedTensor _).flip.mapIso e).symm
  exact preservesFiniteLimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight L).symm

private noncomputable def scalarPresheafFunctor
    {S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) where
  obj M := SheafOfModules.changeOfRingsPresheafOfUniverses.{vC, uC, u, u} α M
  map {M N} f :=
    { app U := (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
      naturality i := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{vC, uC, u, u} α _ f i }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    change (ModuleCat.extendScalars (α.hom.app U).hom).map (𝟙 (M.val.obj U)) = _
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _

private noncomputable def scalarFunctor
    {S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) :=
  scalarPresheafFunctor R α ⋙ PresheafOfModules.sheafification.{u}
    (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) (𝟙 _)

private noncomputable def scalarRawIso
    {S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    scalarPresheafFunctor R α ⋙ PresheafOfModules.toPresheaf _ ≅
      SheafOfModules.forget _ ⋙ tensorLeft
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj
          (SheafOfModules.unit.{vC, uC, u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))).val ⋙
        PresheafOfModules.toPresheaf _ :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun U ↦ Iso.refl _) (by
    intro U V f
    ext z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      exact SheafOfModules.changeOfRingsMap_tmulOfUniverses.{vC, uC, u, u} α M f b m)) (by
    intro M N f
    ext U z
    rfl)

private noncomputable def tensorLeftSheafIso
    (B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    tensorLeft B ≅ SheafOfModules.forget _ ⋙ tensorLeft B.val ⋙
      PresheafOfModules.sheafification.{u} (R :=
        (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let A := PresheafOfModules.sheafification.{u} (R := O) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (R := O) (𝟙 _)
  let I := SheafOfModules.forget.{u} O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)
  let T := tensorLeft B
  let b : A.obj B.val ≅ B := (asIso adj.counit).app B
  let i : A ⋙ T ≅ tensorLeft B.val ⋙ A :=
    Functor.isoWhiskerLeft A ((curriedTensor _).mapIso b.symm) ≪≫
      Functor.Monoidal.commTensorLeft A B.val
  exact (Functor.isoWhiskerRight (asIso adj.counit).symm T) ≪≫
    Functor.isoWhiskerLeft I i

private noncomputable def scalarUnderlyingIso
    {S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    scalarFunctor R α ⋙
      SheafOfModules.toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ≅
      tensorLeft (C := SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj
          (SheafOfModules.unit.{vC, uC, u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⋙
      SheafOfModules.toSheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj
      (SheafOfModules.unit.{vC, uC, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  let t := tensorLeftSheafIso R B
  exact Functor.isoWhiskerRight (scalarRawIso R α) (presheafToSheaf J AddCommGrpCat.{u}) ≪≫
    (Functor.isoWhiskerRight t (SheafOfModules.toSheaf.{u} O)).symm

end Helpers

/-- Actual scalar localization is additive and exact, as is any naturally isomorphic
functor. The object and arrow equalities specify the existing sheafified change of rings;
the existential packages those objects and maps as a functor, without choosing an unrelated
left adjoint.
Source: Stacks Project, Modules on Sites, Tag 03ET and Tags 03DA, 03DB, 03ER, 03ES;
Algebra, Tag 00HT (blueprint: lem-weil-pbc-scalar-localization-sheaf-exact).

Proof:
1. The presheaf `P(V) = R(V)[1/s(V)]` has flat section modules by
   `lem-weil-pbc-localization-flat`, including when a power of the section is zero.
2. Presheaf kernels and finite products are sectionwise. Flat tensoring preserves
   kernels by `lem-weil-pbc-flat-tensor-exact`, and finite products by the coordinate
   inclusion/projection tensor formulas, including the empty product. These formulas
   commute with restrictions, so the presheaf tensor preserves finite limits.
3. Apply `lem-pc-sites-modules-sheafification-flat`: sheafifying P gives the flat
   localization module. Tensor symmetry and `lem-pc-sheaf-modules-tensor-closed`
   give an additive exact endofunctor `T(M) = R_s ⊗_R M` on R-module sheaves.
4. Retaining multiplication on the first factor gives the specified change-of-rings
   objects and maps E. The sectionwise identity on tensors, followed by sheafification,
   identifies restriction of scalars of E with T. The balancing relation identifies
   their R-actions, and the formula `b ⊗ m ↦ b ⊗ f(m)` proves naturality.
5. By `situation-conventions`, forgetting to abelian sheaves
   is faithful and exact and detects exactness. Thus exactness of T proves exactness
   of E in R_s-modules; faithfulness also proves additivity. No surjectivity on sections
   of a sheaf epimorphism is assumed.
6. In the abelian module categories, exactness preserves kernels and cokernels, while
   additivity preserves finite biproducts. The finite-diagram kernel/cokernel formulas
   imply finite-limit and finite-colimit preservation. A natural isomorphism F ≅ E
   conjugates the arrow maps and identifies images of short exact sequences; hence F
   has the same additivity and exactness properties. -/
theorem scalarLocalization_sheaf_exact
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    ∃ (E : ringedSiteModules.{u, u, vC, uC}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        ringedSiteModules.{u, u, vC, uC} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ringedLocalizationRingOfUniverses.{u, uC, vC} (J := J) R s)))
      (hE : ∀ M : ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        E.obj M = SheafOfModules.changeOfRingsOfUniverses.{vC, uC, u, u}
        (ringedLocalizationRingUnitOfUniverses.{u, uC, vC} (J := J) R s) M),
      (∀ {M N : ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : M ⟶ N),
        E.map f = eqToHom (hE M) ≫
          SheafOfModules.changeOfRingsHomOfUniverses.{vC, uC, u, u}
            (ringedLocalizationRingUnitOfUniverses.{u, uC, vC} (J := J) R s) M f ≫
              eqToHom (hE N).symm) ∧
      E.Additive ∧ PreservesFiniteLimits E ∧ PreservesFiniteColimits E ∧
      (∀ F : ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
          ringedSiteModules.{u, u, vC, uC}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (ringedLocalizationRingOfUniverses.{u, uC, vC} (J := J) R s)),
        Nonempty (F ≅ E) →
          F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F) := by
  let α := ringedLocalizationRingUnitOfUniverses.{u, uC, vC} R s
  let S := ringedLocalizationRingOfUniverses.{u, uC, vC} R s
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let OS := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  let E := scalarFunctor R α
  let U := SheafOfModules.toSheaf.{u} OS
  let B := (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj
      (SheafOfModules.unit.{vC, uC, u} OS)
  let T := tensorLeft B
  let e : E ⋙ U ≅ T ⋙ SheafOfModules.toSheaf.{u} O := scalarUnderlyingIso R α
  have : PreservesFiniteLimits T := localization_tensor_flat R s
  have : PreservesFiniteColimits T := inferInstance
  have : PreservesFiniteLimits (T ⋙ SheafOfModules.toSheaf.{u} O) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (T ⋙ SheafOfModules.toSheaf.{u} O) :=
    comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (E ⋙ U) :=
    preservesFiniteLimits_of_natIso (F := T ⋙ SheafOfModules.toSheaf.{u} O) e.symm
  have : PreservesFiniteColimits (E ⋙ U) :=
    preservesFiniteColimits_of_natIso (F := T ⋙ SheafOfModules.toSheaf.{u} O) e.symm
  have : E.Additive := by
    have : (E ⋙ U).Additive := Functor.additive_of_iso e.symm
    exact Functor.additive_of_comp_faithful E U
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E U
  have : PreservesFiniteColimits E := preservesFiniteColimits_of_reflects_of_preserves E U
  refine ⟨E, fun M ↦ rfl, ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro F ⟨i⟩
    exact ⟨Functor.additive_of_iso i.symm,
      preservesFiniteLimits_of_natIso i.symm, preservesFiniteColimits_of_natIso i.symm⟩

end CategoryTheory
