/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.PullbackTensorTotalCompositionLocalized
import WeilConjectures.Algebra.Homology.KFlatPullback

/-! # Normalization of the successive tensor pullback route

Source: Stacks Project, cohomology.tex, Tags 079U, 08HY and 0D5S.
(blueprint: lem-sc-derived-pullback-tensor-successive-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
private theorem normalization_pasting
    {C : Type*} [Category* C] [mC : MonoidalCategory C]
    {D : Type*} [Category* D] [mD : MonoidalCategory D]
    (L : C ⥤ D) {A B A' B' U V T W : C}
    {A₀ B₀ A'' B'' A''' B''' V' T' U' U'' S : D}
    (t : W ⟶ A ⊗ B) (r : W ⟶ U) (e : U ⟶ V) (j : V ⟶ T)
    (a : A ⟶ A') (b : B ⟶ B') (m : A' ⊗ B' ⟶ T)
    (τ₀ : L.obj (A ⊗ B) ⟶ L.obj A ⊗ L.obj B)
    (τ₁ : L.obj (A' ⊗ B') ⟶ L.obj A' ⊗ L.obj B')
    (dA : L.obj A' ⟶ A'') (dB : L.obj B' ⟶ B'')
    (eV : L.obj V ⟶ V') (eT : L.obj T ⟶ T')
    (jF : V' ≅ T') (k : T' ≅ U') (n : A'' ⊗ B'' ⟶ U')
    (wA : A'' ⟶ A''') (wB : B'' ⟶ B''') (n' : A''' ⊗ B''' ⟶ U'')
    (z : V' ⟶ S) (q : S ⟶ U'')
    (iA : L.obj A ⟶ A₀) (iB : L.obj B ⟶ B₀)
    (jA : A₀ ⟶ A''') (jB : B₀ ⟶ B''')
    (hA : iA ≫ jA = L.map a ≫ dA ≫ wA)
    (hB : iB ≫ jB = L.map b ≫ dB ≫ wB)
    (hg : r ≫ e ≫ j = t ≫ (a ⊗ₘ b) ≫ m)
    (hf : L.map m ≫ eT ≫ k.hom = τ₁ ≫ (dA ⊗ₘ dB) ≫ n)
    (ht : L.map (a ⊗ₘ b) ≫ τ₁ = τ₀ ≫ (L.map a ⊗ₘ L.map b))
    (he : L.map j ≫ eT = eV ≫ jF.hom)
    (hc : (wA ⊗ₘ wB) ≫ n' = n ≫ k.inv ≫ jF.inv ≫ z ≫ q) :
    (L.map t ≫ τ₀ ≫ (iA ⊗ₘ iB)) ≫ ((jA ⊗ₘ jB) ≫ n') =
      L.map r ≫ L.map e ≫ eV ≫ z ≫ q := by
  rw [Category.assoc, Category.assoc, tensorHom_comp_tensorHom_assoc]
  rw [hA, hB]
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [hc, ← reassoc_of% ht, ← reassoc_of% hf]
  simp only [← Category.assoc, ← Functor.map_comp]
  have hg' := hg
  simp only [← Category.assoc] at hg'
  rw [← hg']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% he]
  simp

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Normalization of the successive tensor-pullback route on K-flat complexes.
Source: Stacks Project, cohomology.tex, Tags 079U and 0D5S.
(blueprint: lem-sc-derived-pullback-tensor-successive-normalization).

Proof: normalize the g tensorator and the f tensorator by their defining K-flat
coordinate equations. Naturality of the f tensorator moves the g counits to
its inputs. The factorization equation for the composition comparison at P and N
turns the final composite-arrow counits into the successive counits followed by
the ordinary pullback composition maps. Naturality of the localization tensor
map moves these composition maps to the total complex. At each (p,q) summand,
the ordinary tensor composition equation identifies the resulting map with the
given phi: transpose under the pinned tensor-pullback adjunctions and test on
pure tensor sections. Both transposes send s tensor t to the tensor of the same
successive unit images. Tensor universality and the adjunction bijection prove
the module equality; joint epimorphy of the total-complex summand inclusions
proves the chain equality. Localize it. This proves only the successive route's
normalization; comparison with the direct derived tensorator and cancellation
are performed in the importing theorem. Zero complexes and identity morphisms
satisfy the same calculation, as do the unique maps on empty schemes.
-/
theorem derivedPullback_tensor_successive_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hN : N.IsKFlatTensor)
    (φ : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hφ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f ≫ g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal Z P N)
    let β := Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
    ((derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N))) ≫
      ((cast (by rfl) ((SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ⊗ₘ
        cast (by rfl) ((SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N))) ≫
        pullbackTensorModelMap X
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)) =
    (derivedPullback f).map ((derivedPullback g).map (pullbackTensorModelMap Z P N)) ≫
      (derivedPullback f).map (cast (by rfl) ((SingleComplexBaseChange.counit g).app H)) ≫
      (SingleComplexBaseChange.counit f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map (β.hom.app H) ≫
      cast (by rfl) ((DerivedCategory.Q.{w}
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map φ.hom) := by
  classical
  let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) a b
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal Z P N)
  let β := Functor.mapHomotopyCategoryCompIso
    ((conjugateIsoEquiv
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
      (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
  let Pg := ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P
  let Ng := ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N
  have hPg : CochainComplex.IsKFlatTensor (R := Y.sheaf) Pg := by
    convert CochainComplex.isKFlat_pullback g.base Y.sheaf Z.sheaf ⟨g.c⟩ P hP using 1
    rfl
  have hNg : CochainComplex.IsKFlatTensor (R := Y.sheaf) Ng := by
    convert CochainComplex.isKFlat_pullback g.base Y.sheaf Z.sheaf ⟨g.c⟩ N hN using 1
    rfl
  have hg : IsCanonicalPullbackTensorComparison g
      (fun K L ↦ (mixedHomTensorPullbackIso g).hom.app (K, L)) :=
    Classical.choose_spec (exists_mixedHomTensorPullbackIso.{u, w} g)
  have hf : IsCanonicalPullbackTensorComparison f
      (fun K L ↦ (mixedHomTensorPullbackIso f).hom.app (K, L)) :=
    Classical.choose_spec (exists_mixedHomTensorPullbackIso.{u, w} f)
  let ψ := Classical.choose (hg.1 P N hP hN)
  have hψ := (Classical.choose_spec (hg.1 P N hP hN)).1
  have eψ := (Classical.choose_spec (hg.1 P N hP hN)).2
  let θ := Classical.choose (hf.1 Pg Ng hPg hNg)
  have hθ := (Classical.choose_spec (hf.1 Pg Ng hPg hNg)).1
  have eθ := (Classical.choose_spec (hf.1 Pg Ng hPg hNg)).2
  have hchain := pullback_tensor_total_composition_localized f g P N ψ hψ θ hθ φ hφ
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  have : (derivedPullback (f ≫ g)).IsLeftDerivedFunctor
      (SingleComplexBaseChange.counit (f ≫ g)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have fac (R : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
      (c f g).hom.app (DerivedCategory.Q.obj R) ≫
        (SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj R) =
      (derivedPullback f).map ((SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj R)) ≫
        (SingleComplexBaseChange.counit f).app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj R)) ≫
        DerivedCategory.Qh.map (β.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj R)) := by
    let δ :=
      (Functor.associator DerivedCategory.Qh (derivedPullback g) (derivedPullback f)).inv ≫
        Functor.whiskerRight (SingleComplexBaseChange.counit g) (derivedPullback f) ≫
        (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
        Functor.whiskerLeft _ (SingleComplexBaseChange.counit f) ≫
        (Functor.associator _ _
          (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
        Functor.whiskerRight β.hom
          (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    have hnat : Functor.whiskerLeft DerivedCategory.Qh (c f g).hom ≫
        SingleComplexBaseChange.counit (f ≫ g) = δ := by
      rw [show (c f g).hom = _ from hc]
      exact Functor.leftDerived_fac (derivedPullback (f ≫ g))
        (SingleComplexBaseChange.counit (f ≫ g)) (HomotopyCategory.quasiIso _ (.up ℤ))
        (derivedPullback g ⋙ derivedPullback f) δ
    have h := congrArg (fun t ↦ t.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj R)) hnat
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app] at h
    simp only [Category.id_comp] at h
    with_unfolding_all exact h
  have hn := hf.2
    ((derivedPullback g).obj (DerivedCategory.Q.obj P)) (DerivedCategory.Q.obj Pg)
    ((derivedPullback g).obj (DerivedCategory.Q.obj N)) (DerivedCategory.Q.obj Ng)
    ((SingleComplexBaseChange.counit g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    ((SingleComplexBaseChange.counit g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj N))
  have he := (SingleComplexBaseChange.counit f).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map ψ.hom)
  dsimp only [Functor.comp_map] at he
  have h := normalization_pasting (C := schemeDerivedCategory Y)
    (D := schemeDerivedCategory X) (mC := schemeDerivedTensorMonoidal Y)
    (mD := schemeDerivedTensorMonoidal X) (derivedPullback f)
    ((mixedHomTensorPullbackIso g).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N))
    _ _ _ _ _ _
    ((mixedHomTensorPullbackIso f).hom.app
      ((derivedPullback g).obj (DerivedCategory.Q.obj P),
        (derivedPullback g).obj (DerivedCategory.Q.obj N)))
    _ _ _
    ((SingleComplexBaseChange.counit f).app
      (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H)) _
    (DerivedCategory.Q.mapIso
      (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).mapIso ψ))
    (DerivedCategory.Q.mapIso θ) _ _ _ _ _ _ _ _ _ _
    (fac P) (fac N) eψ eθ hn he hchain
  exact h

end AlgebraicGeometry
