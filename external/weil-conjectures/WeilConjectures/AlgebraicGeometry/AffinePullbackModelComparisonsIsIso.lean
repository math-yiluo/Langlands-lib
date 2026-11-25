/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso

/-! # Canonical affine model comparisons

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-pullback-sections-model-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

/-- Equality transport keeps the additive instances in the derived unit aligned. -/
private theorem rightDerivedUnit_isIso_of_functor_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (h : F = G)
    (X : HomotopyCategory C (.up ℤ))
    (hX : IsIso (G.rightDerivedFunctorUnit.app X)) :
    IsIso (F.rightDerivedFunctorUnit.app X) := by
  subst G
  exact hX

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- Canonical comparison from localized sections to derived affine sections.
Source: Stacks Project, Tag 06Z0, ordinary-to-derived comparison. 
(blueprint: new-affine-pullback-model-comparisons-isIso)
-/
def affineModelSectionsComparison (A : CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj
        (((affineGlobalSections (𝟙 (Spec A))).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (affineDerivedGlobalSections (𝟙 (Spec A))).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (affineGlobalSections (𝟙 (Spec A))).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
    (affineGlobalSections (𝟙 (Spec A))).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app K) ≫
    (affineGlobalSectionsDerivedIso (𝟙 (Spec A))).hom.app (DerivedCategory.Q.obj K)

/-- The fixed left-derived counit, transported from homotopy to complex localization.
Source: Stacks Project, Tag 0D5S; the same counit fixes canonicalPullbackAdjunction. 
(blueprint: new-affine-pullback-model-comparisons-isIso)
-/
def affineModelPullbackComparison {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    [(Scheme.Modules.tensorPullback g).Additive]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) ℤ) :
    (derivedPullback g).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj K) :=
  (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _

/-- The two canonical comparison maps used to form the affine pullback sections model
are invertible on a K-flat associated-sheaf complex.
Source: Stacks Project, perfect.tex, Tags 08DV, 08DW(2), and 06Z0.
(blueprint: new-affine-pullback-model-comparisons-isIso).
Proof: translate generic module K-flatness into the acyclic tensor criterion using
HomotopyCategory.kFlat_iff_preserves_acyclic and kFlat_quotient_obj_iff.
Apply isKFlat_tilde to obtain sheaf K-flatness. The counit supplied by
exists_derivedPullback is invertible on this complex. Uniqueness of left-derived
functors compares that counit with the fixed counit of
exists_derivedPullbackComposition; both Q/Qh transport factors are isomorphisms.
For the sections comparison, full faithfulness of Spec writes g as Spec.map of a
ring map. The natural tilde pullback isomorphism identifies termwise pullback of K
with tilde of the scalar-extended complex, compatibly with differentials.
Naturality of the right-derived unit transports its invertibility from
this tilde complex, where affineTildeDerivedSectionsUnit_isIso applies. The other
three factors defining affineModelSectionsComparison are isomorphisms. No
boundedness or flatness of the ring map is used. For the zero complex and zero
rings the same comparison maps are maps between zero objects and remain invertible. -/
theorem affinePullbackModelComparisons_isIso
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    [hT : (tilde.functor R).Additive] [hP : (Scheme.Modules.tensorPullback g).Additive]
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M) :
    let K := (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (tilde.functor R) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M
    IsIso (affineModelPullbackComparison g K) ∧
      IsIso (affineModelSectionsComparison B
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj K)) := by
  classical
  let K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) ℤ :=
    (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (tilde.functor R) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M
  constructor
  · let A := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)
    have hK : CochainComplex.IsKFlatTensor (R := (Spec R).sheaf) K := by
      apply isKFlat_tilde R M
      intro F hF
      have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
        ((HomotopyCategory.quotient _ (.up ℤ)).obj M)).mp
          ((HomotopyCategory.kFlat_quotient_obj_iff M).mpr hM)
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
        (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF)).2
    obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      E, hE, hEmap, hEadd, ε, hL, htri, hflat⟩ :=
      (derivedPullback_spec g)
    have hEq : E = Scheme.Modules.tensorPullback g :=
      CategoryTheory.Functor.ext hE (fun _ _ a ↦ hEmap a)
    clear hE hEmap hI hImap hIadd hIlim hIcolim hIres I htri
    subst E
    have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)) := hflat K hK
    let ε' := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g
    have hL' := (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g
    change (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (.up ℤ)) at hL
    have : (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso A (.up ℤ)) := hL
    have : (derivedPullback g).IsLeftDerivedFunctor ε'
        (HomotopyCategory.quasiIso A (.up ℤ)) := hL'
    have hl : IsIso ((derivedPullback g).leftDerivedLift ε'
        (HomotopyCategory.quasiIso A (.up ℤ)) (derivedPullback g) ε) :=
      ((derivedPullback g).isLeftDerivedFunctor_iff_isIso_leftDerivedLift ε'
        (HomotopyCategory.quasiIso A (.up ℤ)) (derivedPullback g) ε).mp hL
    have hfac := (derivedPullback g).leftDerived_fac_app ε'
      (HomotopyCategory.quasiIso A (.up ℤ)) (derivedPullback g) ε
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)
    have : IsIso (ε'.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)) :=
      IsIso.of_isIso_fac_left hfac
    dsimp only [affineModelPullbackComparison]
    infer_instance
  · clear hM
    obtain ⟨φ, hg⟩ : ∃ φ : R ⟶ B, Spec.map φ = g :=
      ⟨(Spec.fullyFaithful.preimage g).unop, Spec.fullyFaithful.map_preimage g⟩
    subst g
    have : (tilde.functor B).Additive := ⟨by intros; exact tilde.map_add _ _⟩
    let E := ModuleCat.extendScalars φ.hom
    have : E.IsLeftAdjoint := ⟨_, ⟨ModuleCat.extendRestrictScalarsAdj φ.hom⟩⟩
    have : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ E
      (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
    obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso φ
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (.up ℤ)
    let S := affineGlobalSections (𝟙 (Spec B))
    let N := (E.mapHomologicalComplex (.up ℤ)).obj M
    let δ :
        ((Scheme.Modules.tensorPullback (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj K ≅
        ((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj N :=
      (NatIso.mapHomologicalComplex θ (.up ℤ)).app M
    have hu := affineTildeDerivedSectionsUnit_isIso B
      ((HomotopyCategory.quotient _ (.up ℤ)).obj N)
    have hu' : IsIso (S.rightDerivedFunctorUnit.app
        (q.obj (((tilde.functor B).mapHomologicalComplex (.up ℤ)).obj N))) := by
      have hS : S = (RingedSpace.globalSectionsFunctor (Spec B).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso B).inv.hom) := by
        dsimp only [S, affineGlobalSections, affineGlobalSectionsRestriction]
        rw [Scheme.Hom.id_appTop, Category.comp_id]
      exact rightDerivedUnit_isIso_of_functor_eq S _ hS _ hu
    have : IsIso (S.rightDerivedFunctorUnit.app
        (q.obj (((Scheme.Modules.tensorPullback (Spec.map φ)).mapHomologicalComplex
          (.up ℤ)).obj K))) :=
      (NatTrans.isIso_app_iff_of_iso S.rightDerivedFunctorUnit (q.mapIso δ)).mpr hu'
    dsimp only [affineModelSectionsComparison]
    infer_instance

end AlgebraicGeometry
