/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
import WeilConjectures.AlgebraicGeometry.ConnectiveSingleHom
import WeilConjectures.FromJoel.Algebra.Homology.Single
import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseModelComparison

/-! # Derived test sections and ordinary connective cycles

## References

* Stacks Project, Tags 06YJ and 0D5S
* Tag 05RR, truncation calculus of fractions
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private noncomputable def singleCyclesEquiv {C : Type*} [Category C] [Abelian C]
    (M : C) (P : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj M ⟶ P) ≃+
      AddMonoidHom.ker
        ({ toFun := fun f : M ⟶ P.X 0 ↦ f ≫ P.d 0 1
           map_zero' := by simp
           map_add' := fun f g ↦ by simp only [Preadditive.add_comp] } :
          (M ⟶ P.X 0) →+ (M ⟶ P.X 1)) :=
  { HomologicalComplex.fromSingleEquiv M P 0 1 (by simp) with
    map_add' := by
      intro f g
      apply Subtype.ext
      change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ (f + g).f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ f.f 0 +
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ g.f 0
      simp [Preadditive.comp_add] }

private noncomputable def isoHomAddEquiv {C : Type*} [Category C] [Preadditive C]
    {X Y X' Y' : C} (a : X ≅ X') (b : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toFun f := a.inv ≫ f ≫ b.hom
  invFun f := a.hom ≫ f ≫ b.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.comp_add, Preadditive.add_comp]

private noncomputable def localizationEquiv {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{v} C] (M : C) (P : CochainComplex C ℤ)
    (hneg : ∀ i : ℤ, i < 0 → IsZero (P.X i)) :
    ((CochainComplex.singleFunctor C 0).obj M ⟶ P) ≃+
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj M) ⟶
        DerivedCategory.Q.obj P) :=
  AddEquiv.ofBijective DerivedCategory.Q.mapAddHom
    (DerivedCategory.connective_single_hom_bijective M P hneg)

-- Comparing termwise tensor models unfolds several layers of sheaf functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a fixed connective strictly perfect model, test sections are ordinary
cycles on every scheme mapping through its open domain. The comparison is natural
for the canonical composition maps. No affine, scalar-basis or residue hypothesis
is used. -/
theorem picard_connective_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t →
          picardDerivedModelSections E t ≃+ picardOrdinaryModelCycles W U K t s,
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t')
        (ξ : picardDerivedModelSections E t),
        (q t' s' hf' (picardDerivedModelRestriction E i t t' ht ξ)).val =
          picardOrdinaryModelRestriction W U K i t t' s s' ht hs
            (q t s hf ξ).val := by
  classical
  obtain ⟨a, b, hab⟩ := picard_termwise_model_comparison W E U K hK hE
  have hP {T : Scheme.{v}} (s : T ⟶ U.toScheme) :
      ∀ i : ℤ, i < 0 → IsZero ((picardTermwiseModel W U K s).X i) := by
    intro i hi
    let : (Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    let : (Modules.tensorPullback s).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction s)).left_adjoint_additive
    exact (Modules.tensorPullback s).map_isZero
      ((Modules.overEquiv U).functor.map_isZero (hneg i hi))
  let l {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme) :
      (picardTermwiseSource t ⟶ picardTermwiseModel W U K s) ≃+
        ((DerivedCategory.Q (C := SheafOfModules.{v}
          (moduleRings T.toRingedSpace))).obj (picardTermwiseSource t) ⟶
          (DerivedCategory.Q (C := SheafOfModules.{v}
            (moduleRings T.toRingedSpace))).obj (picardTermwiseModel W U K s)) :=
    @localizationEquiv _ _ _
      (inferInstance : HasDerivedCategory.{v + 1}
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)))
      ((Modules.tensorPullback t).obj (SheafOfModules.unit (moduleRings W.toRingedSpace)))
      (picardTermwiseModel W U K s) (hP s)
  let c {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme) :=
    singleCyclesEquiv
      ((Modules.tensorPullback t).obj (SheafOfModules.unit (moduleRings W.toRingedSpace)))
      (picardTermwiseModel W U K s)
  let q {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme) (hf : s ≫ U.ι = t) :
      picardDerivedModelSections E t ≃+ picardOrdinaryModelCycles W U K t s :=
    ((isoHomAddEquiv (a t) (b t s hf)).trans (l t s).symm).trans (c t s)
  refine ⟨fun t s hf ↦ q t s hf, ?_⟩
  intro T T' i t t' s s' ht hs hf hf' ξ
  let f := (l t s).symm (isoHomAddEquiv (a t) (b t s hf) ξ)
  have hξ : (a t).hom ≫ DerivedCategory.Q.map f ≫ (b t s hf).inv = ξ := by
    change (isoHomAddEquiv (a t) (b t s hf)).symm ((l t s) f) = ξ
    simp only [f, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  obtain ⟨f', hcomp, hres⟩ := hab i t t' s s' ht hs hf hf' f
  rw [hξ] at hres
  have hchain : (l t' s').symm
      (isoHomAddEquiv (a t') (b t' s' hf')
        (picardDerivedModelRestriction E i t t' ht ξ)) = f' := by
    rw [hres]
    change (l t' s').symm
      ((isoHomAddEquiv (a t') (b t' s' hf'))
        ((isoHomAddEquiv (a t') (b t' s' hf')).symm ((l t' s') f'))) = f'
    simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  change ((c t' s') ((l t' s').symm
    (isoHomAddEquiv (a t') (b t' s' hf')
      (picardDerivedModelRestriction E i t t' ht ξ)))).val =
    picardOrdinaryModelRestriction W U K i t t' s s' ht hs ((c t s) f).val
  rw [hchain]
  exact hcomp

end AlgebraicGeometry.Scheme
