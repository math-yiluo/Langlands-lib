/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.RingHomExtensionDefs
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option linter.privateModule false

/-!
# Nilpotent derived reduction detects an upper cohomological bound

Source: Stacks Project, More on Algebra, Tag 0H75,
lemma-check-tor-dimension-modulo-nilpotent, upper-bound-only adaptation used by Tag 09AR
(auxiliary; not a blueprint node).

Ordinary modules are encoded on the existing one-object site with bottom topology.
The additive scalar-extension functor and its left derived functor are specified by
exactly the object formula, morphism formula and universal property supplied by
`SheafOfModules.derivedChangeOfRings`; no choice of a particular model is required.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The one-object site is explicitly equivalent to ordinary modules.
private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := Opposite.op ⟨PUnit.unit⟩

private noncomputable abbrev pointEval (A : Type u) [CommRing A] :
    RingSiteModules A ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)) point

private noncomputable def pointConstant (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ RingSiteModules A where
  obj M := ⟨{ obj := fun _ ↦ M
              map := fun _ ↦ ModuleCat.ofHom (LinearMap.id) }, Presheaf.isSheaf_bot _⟩
  map f := ⟨{ app := fun _ ↦ f }⟩

private noncomputable def pointUnitIso {A : Type u} [CommRing A]
    (M : RingSiteModules A) : M ≅ (pointConstant A).obj ((pointEval A).obj M) := by
  let e : M.val ≅ ((pointConstant A).obj ((pointEval A).obj M)).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      obtain rfl : U = point := Subsingleton.elim _ _
      exact Iso.refl _) (by
        intro U V g
        obtain rfl : U = point := Subsingleton.elim _ _
        obtain rfl : V = point := Subsingleton.elim _ _
        obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
        ext x
        simp [pointConstant, pointEval]
        rfl)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso e

private noncomputable def pointEquivalence (A : Type u) [CommRing A] :
    RingSiteModules A ≌ ModuleCat.{u} A where
  functor := pointEval A
  inverse := pointConstant A
  unitIso := NatIso.ofComponents pointUnitIso (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    rfl)
  counitIso := Iso.refl _

private noncomputable local instance pointEval_isEquivalence (A : Type u) [CommRing A] :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private noncomputable local instance pointConstant_isEquivalence (A : Type u) [CommRing A] :
    (pointConstant A).IsEquivalence := (pointEquivalence A).isEquivalence_inverse

private local instance pointConstant_additive (A : Type u) [CommRing A] :
    (pointConstant A).Additive where
  map_add := by intros; rfl

private local instance pointEval_additive (A : Type u) [CommRing A] :
    (pointEval A).Additive where
  map_add := by intros; rfl

private local instance pointExtend_additive
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ρ).left_adjoint_additive

private theorem nilpotent_module_devissage
    {A : Type u} [CommRing A] (I : Ideal A) (T : ModuleCat.{u} A → Prop)
    (hzero : ∀ M, IsZero M → T M)
    (hext : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact →
      T S.X₁ → T S.X₃ → T S.X₂)
    (hbase : ∀ M : ModuleCat.{u} A, (∀ a ∈ I, ∀ m : M, a • m = 0) → T M)
    (n : ℕ) : ∀ M : ModuleCat.{u} A,
      (∀ a ∈ I ^ n, ∀ m : M, a • m = 0) → T M := by
  induction n with
  | zero =>
    intro M hM
    apply hzero M
    apply (IsZero.iff_id_eq_zero M).2
    ext m
    simpa using hM 1 (by simp) m
  | succ n ih =>
    intro M hM
    let L : Submodule A M := I • (⊤ : Submodule A M)
    let S : ShortComplex (ModuleCat.{u} A) :=
      ShortComplex.mk (ModuleCat.ofHom L.subtype) (ModuleCat.ofHom L.mkQ)
        (by ext m; simp)
    have hS : S.ShortExact := by
      apply ModuleCat.shortComplex_shortExact
      · intro m
        change L.mkQ m = 0 ↔ ∃ x : L, L.subtype x = m
        simp
      · exact L.injective_subtype
      · exact L.mkQ_surjective
    apply hext S hS
    · apply ih (ModuleCat.of A L)
      intro a ha x
      apply Subtype.ext
      change a • (x : M) = 0
      refine Submodule.smul_induction_on x.property ?_ ?_
      · intro r hr m _
        rw [← mul_smul]
        apply hM (a * r)
        simpa only [pow_succ] using Ideal.mul_mem_mul ha hr
      · intro x y hx hy
        simp only [smul_add, hx, hy, add_zero]
    · apply hbase (ModuleCat.of A (M ⧸ L))
      intro a ha m
      obtain ⟨x, rfl⟩ := L.mkQ_surjective m
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero L).2
        (Submodule.smul_mem_smul ha (Submodule.mem_top : x ∈ (⊤ : Submodule A M)))

private noncomputable def moduleTensorComplex {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj M := ((MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P
  map f := (NatTrans.mapHomologicalComplex
    ((MonoidalCategory.curriedTensor _).map f) (.up ℤ)).app P
  map_id M := by ext i; simp
  map_comp f g := by ext i; simp

private theorem module_kFlat_of_acyclic_tensor
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro L hL
  obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor L P (curriedTensor _))).2 (hP L hL)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

private theorem module_tensor_upper_bound
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero (P.homology i))
    (M : ModuleCat.{u} A) :
    ∀ i : ℤ, b < i → IsZero (((moduleTensorComplex P).obj M).homology i) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  have : P.IsLE b := (P.isLE_iff b).2 fun i hi ↦
    (HomologicalComplex.exactAt_iff_isZero_homology P i).2 (hb i hi)
  have : (Q.obj P).IsLE b := inferInstance
  have h := isLE_tensor (Q.obj P) ((singleFunctor _ 0).obj M) b 0
  have : (Q.obj (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P)).IsLE b := by
    simpa only [add_zero] using TStructure.t.isLE_of_iso
      (QObjTensorSingleFunctorObjIso P hP M) (b + 0)
  have h' : CochainComplex.IsLE
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) b :=
    (isLE_Q_obj_iff _ b).1 inferInstance
  intro i hi
  have e := (NatIso.mapHomologicalComplex
    (BraidedCategory.tensorLeftIsoTensorRight M) (.up ℤ)).app P
  exact (CochainComplex.exactAt_of_isLE _ b i hi).isZero_homology.of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso e)

private theorem flat_tensor_nilpotent_devissage
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hflat : ∀ i : ℤ, Module.Flat A (P.X i)) (b : ℤ)
    (hbase : ∀ M : ModuleCat.{u} A, (∀ a ∈ I, ∀ m : M, a • m = 0) →
      ∀ i : ℤ, b < i → IsZero (((moduleTensorComplex P).obj M).homology i)) :
    ∀ i : ℤ, b < i → IsZero (P.homology i) := by
  let T := moduleTensorComplex P
  have : T.Additive := by
    constructor
    intro M N f g
    ext i : 1
    change (f + g) ▷ P.X i = f ▷ P.X i + g ▷ P.X i
    simp
  have hzero (M : ModuleCat.{u} A) (hM : IsZero M) :
      ∀ i : ℤ, b < i → IsZero ((T.obj M).homology i) := by
    intro i _
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero ((MonoidalCategory.tensorRight (P.X i)).obj M)
    exact Functor.map_isZero _ hM
  have hext (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
      (h₁ : ∀ i : ℤ, b < i → IsZero ((T.obj S.X₁).homology i))
      (h₃ : ∀ i : ℤ, b < i → IsZero ((T.obj S.X₃).homology i)) :
      ∀ i : ℤ, b < i → IsZero ((T.obj S.X₂).homology i) := by
    have hcomplex : (S.map T).ShortExact := by
      apply HomologicalComplex.shortExact_of_degreewise_shortExact
      intro i
      have := hflat i
      change (S.map (MonoidalCategory.tensorRight (P.X i))).ShortExact
      exact hS.map_of_exact (MonoidalCategory.tensorRight (P.X i))
    intro i hi
    exact (hcomplex.homology_exact₂ i).isZero_X₂
      ((h₁ i hi).eq_of_src _ _) ((h₃ i hi).eq_of_tgt _ _)
  have hunit := nilpotent_module_devissage I
    (fun M ↦ ∀ i : ℤ, b < i → IsZero ((T.obj M).homology i)) hzero hext hbase N
      (ModuleCat.of A A) (by
        intro a ha m
        have ha' : a = 0 := by simpa [hI] using ha
        simp [ha'])
  intro i hi
  have e : T.obj (ModuleCat.of A A) ≅ P :=
    (NatIso.mapHomologicalComplex (MonoidalCategory.leftUnitorNatIso
      (ModuleCat.{u} A)) (.up ℤ)).app P ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P
  exact (hunit i hi).of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso e.symm)

-- The filtration argument for ordinary modules, before transporting it to the site.
private theorem ordinary_nilpotent_upper_bound
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hflat : ∀ i : ℤ, Module.Flat A (P.X i))
    (hP : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic)
    (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero
      ((((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P).homology i)) :
    ∀ i : ℤ, b < i → IsZero (P.homology i) := by
  let q := Ideal.Quotient.mk I
  let Q := ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  have hQ := module_kFlat_of_acyclic_tensor Q
    (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat q P hP)
  apply flat_tensor_nilpotent_devissage I N hI P hflat b
  intro M hM
  have ht : Module.IsTorsionBySet A M I := fun {m a} ↦ hM a a.property m
  let := ht.module
  let M' : ModuleCat.{u} (A ⧸ I) := ModuleCat.of (A ⧸ I) M
  let res := ModuleCat.restrictScalars q
  let eM : res.obj M' ≅ M :=
    (show res.obj M' ≃ₗ[A] M from
      { AddEquiv.refl M with map_smul' := fun _ _ ↦ rfl }).toModuleIso
  obtain ⟨e, he⟩ := ModuleCat.exists_tensorRestrictExtend_module_natural q
  let e' : ((tensorLeft M' ⋙ res).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((tensorLeft (res.obj M')).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ e M' (P.X i)) (by
      intro i j hij
      exact (he M' M' (P.X i) (P.X j) (𝟙 _) (P.d i j)).symm)
  let e'' := (NatIso.mapHomologicalComplex
    ((curriedTensor _).mapIso eM) (.up ℤ)).app P
  intro i hi
  have hz := module_tensor_upper_bound Q hQ b hb M' i hi
  have hr := res.map_isZero hz
  let eh' := (res.mapHomologicalComplexHomologyIso (.up ℤ) i).app
    (((tensorLeft M').mapHomologicalComplex (.up ℤ)).obj Q)
  exact hr.of_iso (((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (e' ≪≫ e'')).symm ≪≫ eh')

end DerivedCategory
