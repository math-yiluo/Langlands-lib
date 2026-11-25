/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # A fixed module resolution computes Ext from the structure sheaf

Source: Stacks Project, Cohomology, Tags 01DZ and 0B6A.
(blueprint: lem-sc-module-resolution-homology-ext).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

local instance moduleResolution_enoughInjectives :
    EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
local instance moduleResolution_hasExt : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{u, u, u + 1} (SheafOfModules.{u} X.ringCatSheaf)

-- The following quotient computation follows the proved private helpers in
-- Sheaf.Paper.ObjectCohomologyResolutionCocycleEquivalence. They are reproduced
-- locally because that module exposes only its abelian-sheaf specialization.
private abbrev nonnegativeHomComplex
    {A : Type (u + 1)} [Category.{u} A] [Preadditive A]
    (X : A) (K : CochainComplex A ℕ) :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj K

private theorem extMk_zero_degree_iff
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    {X F : A} (I : InjectiveResolution F) (a : X ⟶ I.cocomplex.X 0)
    (ha : a ≫ I.cocomplex.d 0 1 = 0) :
    I.extMk a 1 rfl ha = 0 ↔ a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    rw [← I.extEquivCohomologyClass.apply_eq_iff_eq,
      I.extEquivCohomologyClass_extMk, I.extEquivCohomologyClass_zero,
      CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
    rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
      _ _ _ _ _ (-1) (by norm_num)]
    have hz := CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by norm_num)
    constructor
    · rintro ⟨g, hg⟩
      have hgz : g = 0 := hz.eq_of_tgt _ _
      rw [hgz, CategoryTheory.Limits.zero_comp] at hg
      exact (cancel_mono (I.cochainComplexXIso 0 0 rfl).inv).mp (by simpa using hg.symm)
    · rintro rfl
      exact ⟨0, by simp⟩

private theorem homCycle_closed
    {A : Type (u + 1)} [Category.{u} A] [Preadditive A]
    (X : A) (K : CochainComplex A ℕ) (q : ℕ)
    (a : ((nonnegativeHomComplex X K).sc q).g.hom.ker) :
    a.val ≫ K.d q (q + 1) = 0 := by
  have ha := a.property
  change a.val ≫ K.d q ((ComplexShape.up ℕ).next q) = 0 at ha
  rwa [CochainComplex.next ℕ q] at ha

private noncomputable def homCyclesToExt
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    ((nonnegativeHomComplex X I.cocomplex).sc q).g.hom.ker →+ Abelian.Ext X F q where
  toFun a := I.extMk a.val (q + 1) rfl (homCycle_closed X I.cocomplex q a)
  map_zero' := I.extMk_zero _ _
  map_add' a b := (I.add_extMk a.val b.val _ _ _ _).symm

private theorem homCyclesToExt_surjective
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    Function.Surjective (homCyclesToExt X F I q) := by
  intro x
  obtain ⟨a, ha, h⟩ := I.extMk_surjective x (q + 1) rfl
  refine ⟨⟨a, ?_⟩, h⟩
  change a ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
  rwa [CochainComplex.next ℕ q]

private theorem homCyclesToExt_kernel
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    ((nonnegativeHomComplex X I.cocomplex).sc q).abToCycles.range =
      (homCyclesToExt X F I q).ker := by
  ext a
  change (∃ b, ((nonnegativeHomComplex X I.cocomplex).sc q).abToCycles b = a) ↔
    I.extMk a.val (q + 1) rfl (homCycle_closed X I.cocomplex q a) = 0
  simp only [Subtype.ext_iff]
  change (∃ b : X ⟶ I.cocomplex.X ((ComplexShape.up ℕ).prev q),
    b ≫ I.cocomplex.d ((ComplexShape.up ℕ).prev q) q = a.val) ↔ _
  cases q with
  | zero =>
    rw [CochainComplex.prev_nat_zero, extMk_zero_degree_iff]
    have hd : I.cocomplex.d 0 0 = 0 := I.cocomplex.shape _ _ (by simp)
    erw [hd]
    simp only [CategoryTheory.Limits.comp_zero]
    exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨0, h.symm⟩⟩
  | succ p =>
    rw [CochainComplex.prev_nat_succ, I.extMk_eq_zero_iff _ _ _ _ p rfl]

private theorem injectiveResolution_homology_cocycle
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    (X F : A) (I : InjectiveResolution F) (q : ℕ) :
    ∃ (e : Abelian.Ext X F q ≃+ (nonnegativeHomComplex X I.cocomplex).homology q),
      ∀ (a : X ⟶ I.cocomplex.X q) (ha : a ≫ I.cocomplex.d q (q + 1) = 0),
        e (I.extMk a (q + 1) rfl ha) =
          ((nonnegativeHomComplex X I.cocomplex).homologyπ q).hom
            (((nonnegativeHomComplex X I.cocomplex).sc q).abCyclesIso.inv
              ⟨a, by
                change a ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
                rw [CochainComplex.next ℕ q]
                exact ha⟩) := by
  set_option backward.isDefEq.respectTransparency false in
    let K := nonnegativeHomComplex X I.cocomplex
    let S := K.sc q
    let t := QuotientAddGroup.liftEquiv S.abToCycles.range
      (homCyclesToExt_surjective X F I q) (homCyclesToExt_kernel X F I q)
    let d := S.abHomologyIso.addCommGroupIsoToAddEquiv
    refine ⟨t.symm.trans d.symm, ?_⟩
    intro a ha
    let z : S.g.hom.ker := ⟨a, by
      change a ≫ I.cocomplex.d q ((ComplexShape.up ℕ).next q) = 0
      rwa [CochainComplex.next ℕ q]⟩
    apply (t.symm.trans d.symm).symm.injective
    erw [AddEquiv.symm_apply_apply]
    change I.extMk a (q + 1) rfl ha =
      t (S.abHomologyIso.hom (K.homologyπ q (S.abCyclesIso.inv z)))
    change _ = t (((S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom).hom) z)
    change _ = t (((S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
      S.abLeftHomologyData.homologyIso.hom).hom) z)
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl

-- Evaluation at the terminal open, with inverse given by restrictions.
-- This construction also occurs privately in DQCoheratorAdjunction.
private noncomputable def unitSectionsEquiv (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    (SheafOfModules.unit (moduleRings Y.toRingedSpace) ⟶ M) ≃+
      (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M where
  toFun f := (M.unitHomEquiv f).val (Opposite.op ⊤)
  invFun a := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      rfl))
  left_inv f := by
    apply M.unitHomEquiv.injective
    apply Subtype.ext
    funext U
    simp only [Equiv.apply_symm_apply]
    exact (M.unitHomEquiv f).property _
  right_inv a := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val (Opposite.op ⊤) = a
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 _) a = a
    simp
  map_add' f g := by
    change (f.val.app (Opposite.op ⊤) + g.val.app (Opposite.op ⊤))
      (1 : (moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤)) = _
    rfl

private noncomputable def unitSectionComplexIso
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℕ) :
    nonnegativeHomComplex (SheafOfModules.unit X.ringCatSheaf) I ≅
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace) ⋙
        forget₂ _ AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (unitSectionsEquiv X (I.X n)).toAddCommGrpIso) (by
      intro i j _
      ext a
      rfl)

private lemma forget_homologyπ
    {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{u} R)) :
    (S.map (forget₂ _ AddCommGrpCat)).homologyπ ≫
        (S.mapHomologyIso (forget₂ _ AddCommGrpCat)).hom =
      (S.mapCyclesIso (forget₂ _ AddCommGrpCat)).hom ≫
        (forget₂ _ AddCommGrpCat).map S.homologyπ := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq U, h.mapCyclesIso_eq U]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change (h.map U).cyclesIso.hom ≫ U.map h.π ≫ U.map h.homologyIso.inv =
    ((h.map U).cyclesIso.hom ≫ U.map h.cyclesIso.inv) ≫ U.map S.homologyπ
  rw [Category.assoc, ← U.map_comp, h.π_comp_homologyIso_inv, U.map_comp]

/-- A single fixed injective module resolution computes Ext from the structure sheaf.
Source: Stacks Project, Cohomology, Tag 01DZ (cohomology of modules) and Tag 0B6A
(cohomology as Ext from the structure sheaf).
(blueprint: lem-sc-module-resolution-homology-ext).

Proof: An O-linear map from the structure sheaf is determined by the image of 1
on the whole space. Conversely a global section defines such a map by multiplying
its restrictions by local functions. These maps are inverse and additive, and
commute with the differentials of I. Thus cocycles in the sections complex identify
with cocycle maps from the structure sheaf into I. Under this identification,
boundaries identify with null-homotopic cocycle maps: in positive degree they are
maps factoring through the preceding differential, and in degree zero both boundary
subgroups are zero. Mathlib
I.extMk_eq_zero_iff identifies this subgroup with the kernel of the additive map
from cocycle morphisms to Ext, and I.extMk_surjective proves that map is onto.
The quotient is therefore additively equivalent to Ext. Transport its inverse
through the section-complex isomorphism and the homology comparison for the
module-to-abelian-group forgetful functor. Naturality of homology projection
proves the displayed formula. It also uniquely determines the equivalence
because every homology class has a cycle representative. The argument includes
zero modules and the empty scheme, where both groups are zero. No comparison
between different resolutions is asserted here. -/
theorem moduleResolutionHomologyExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf)
    (I : InjectiveResolution F) (n : ℕ) :
    ∃ e : (RingedSpace.globalSectionsComplex I).homology n ≃+
        Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n,
      ∀ (a : (RingedSpace.globalSectionsComplex I).cycles n)
        (φ : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
        (hφ : φ ≫ I.cocomplex.d n (n + 1) = 0),
        φ.val.app (op ⊤) (1 : Γ(X, ⊤)) =
          (RingedSpace.globalSectionsComplex I).iCycles n a →
        e ((RingedSpace.globalSectionsComplex I).homologyπ n a) =
          I.extMk φ (n + 1) rfl hφ := by
  let A := SheafOfModules.unit X.ringCatSheaf
  obtain ⟨e, he⟩ := injectiveResolution_homology_cocycle A F I n
  let K := RingedSpace.globalSectionsComplex I
  let U := forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat
  let c := unitSectionComplexIso I.cocomplex
  let h := (HomologicalComplex.homologyFunctor _ _ n).mapIso c
  let d := (K.sc n).mapHomologyIso U
  refine ⟨(e.trans (h ≪≫ d).addCommGroupIsoToAddEquiv).symm, ?_⟩
  intro a φ hφ ha
  apply (e.trans (h ≪≫ d).addCommGroupIsoToAddEquiv).injective
  erw [AddEquiv.apply_symm_apply]
  change K.homologyπ n a = d.hom (h.hom (e (I.extMk φ (n + 1) rfl hφ)))
  rw [he φ hφ]
  let z := ((nonnegativeHomComplex A I.cocomplex).sc n).abCyclesIso.inv
    ⟨φ, by
      change φ ≫ I.cocomplex.d n ((ComplexShape.up ℕ).next n) = 0
      rwa [CochainComplex.next ℕ n]⟩
  let b := HomologicalComplex.cyclesMap c.hom n z
  have hb : ((K.sc n).mapCyclesIso U).hom b = a := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    change (U.map (K.iCycles n)) (((K.sc n).mapCyclesIso U).hom b) = _
    change (((K.sc n).mapCyclesIso U).hom ≫ U.map (K.iCycles n)) b = _
    erw [ShortComplex.mapCyclesIso_hom_iCycles]
    change (((HomologicalComplex.cyclesMap c.hom n) ≫
      ((U.mapHomologicalComplex (.up ℕ)).obj K).iCycles n) z) = _
    erw [HomologicalComplex.cyclesMap_i]
    change (c.hom.f n) ((nonnegativeHomComplex A I.cocomplex).iCycles n z) = _
    dsimp only [z, HomologicalComplex.iCycles]
    erw [((nonnegativeHomComplex A I.cocomplex).sc n).abCyclesIso_inv_apply_iCycles]
    exact ha
  change K.homologyπ n a =
    (((nonnegativeHomComplex A I.cocomplex).homologyπ n ≫
      HomologicalComplex.homologyMap c.hom n) ≫ d.hom) z
  rw [HomologicalComplex.homologyπ_naturality]
  change K.homologyπ n a =
    ((((U.mapHomologicalComplex (.up ℕ)).obj K).homologyπ n) ≫ d.hom) b
  erw [forget_homologyπ (K.sc n)]
  change K.homologyπ n a = K.homologyπ n (((K.sc n).mapCyclesIso U).hom b)
  rw [hb]

end
end AlgebraicGeometry.Scheme.Modules
