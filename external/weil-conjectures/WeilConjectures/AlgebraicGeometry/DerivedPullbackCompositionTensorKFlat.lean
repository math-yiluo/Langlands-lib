/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import all WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization

/-! # Tensor compatibility of derived pullback composition on K-flat complexes

Source: Stacks Project, cohomology.tex, Tags 079U, 08HY and 0D5S.
(blueprint: lem-sc-derived-pullback-composition-tensor-kflat).
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
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

-- The selected counits and tensor model maps have large dependent types.
/-- The fixed composition comparison preserves the normalized tensorator on
localized K-flat complexes.
Source: Stacks Project, cohomology.tex, Lemma 079U and Remark 08HY;
composition of derived pullbacks as in Tag 0D5S.
(blueprint: lem-sc-derived-pullback-composition-tensor-kflat).

Proof: use the normalization equations of the three tensorators at P and N.
Their tensors and their termwise pullbacks are K-flat, so all localization tensor
maps and derived counits in those equations are invertible. The shared counit is
precisely the epsilon chosen by exists_derivedPullbackComposition, so c and the
tensorators have the same normalization. The defining leftDerivedLift equation for c identifies
its composite with the counit of the
composite arrow with the successive counits followed by the localized termwise
composition comparison. Use naturality of c for the invertible localization map
mu_Z(P,N) to replace c at Q(P) tensor Q(N) by c at Q(Tot(P tensor N)). Use naturality
of the f-tensorator in epsilon_g(P), epsilon_g(N) to replace its inputs Lg Q(P),
Lg Q(N) by Q(g*P), Q(g*N). Postcompose the two routes with the tensor of the
composite-arrow counits and the target localization tensor map. Substitute the
c-factorization at P, N and Tot(P tensor N), then the g-, f- and fg-tensorator
normalization equations. The input localization map and all these output maps
are invertible; the cancellations identify the equation with the localized
ordinary chain-map tensor/composition equation. The remaining equality is an equality of
chain maps from the pullback of the total tensor complex. In each total degree,
test on every summand P^p tensor N^q. The normalization of the chain tensorators
identifies these maps with the ordinary tensor-pullback tensorators; the termwise
composition map is the mate of pushforwardComp under the pinned tensor-pullback
adjunctions. On pulled-back pure tensor sections, both routes give the tensor
of the same twice-pulled-back sections, because the composite adjunction unit
is the successive unit. The adjunction Hom bijection and the tensor universal
property give equality of the module maps, hence of the chain maps. Localize
this equality and undo the cancellations. This is a triangle for two composable
arrows, with no cartesian square, equality transport, inverse comparison or
extension to arbitrary derived inputs. Zero complexes, identity arrows, and
empty schemes require no separate assumptions. -/
theorem derivedPullbackComposition_tensor_kFlat
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hN : N.IsKFlatTensor) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    (derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N)) =
    (c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫
      (mixedHomTensorPullbackIso (f ≫ g)).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) := by
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
  have hτ : IsCanonicalPullbackTensorComparison (f ≫ g)
      (fun K L ↦ (mixedHomTensorPullbackIso (f ≫ g)).hom.app (K, L)) :=
    Classical.choose_spec (exists_mixedHomTensorPullbackIso.{u, w} (f ≫ g))
  have hflat := hτ.1
  have hmodels := hflat P N hP hN
  rcases hmodels with ⟨φ, hφ, heq⟩
  have hpull : CochainComplex.IsKFlatTensor (R := X.sheaf)
      (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P) := by
    convert CochainComplex.isKFlat_pullback (f ≫ g).base X.sheaf Z.sheaf
      ⟨(f ≫ g).c⟩ P hP using 1
    with_unfolding_all rfl
  have := counit_isIso (f ≫ g) P hP
  have := counit_isIso (f ≫ g) N hN
  have := modelMap_isIso X
    (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
    (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N) hpull
  apply (cancel_mono
    (((SingleComplexBaseChange.counit (f ≫ g)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
      (SingleComplexBaseChange.counit (f ≫ g)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
      pullbackTensorModelMap X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))).1
  have hl := derivedPullback_tensor_successive_normalization f g P N hP hN φ hφ
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  have : (derivedPullback (f ≫ g)).IsLeftDerivedFunctor
      (SingleComplexBaseChange.counit (f ≫ g)) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have fac : (c f g).hom.app (DerivedCategory.Q.obj (pullbackTensorTotal Z P N)) ≫
      (SingleComplexBaseChange.counit (f ≫ g)).app H =
    (derivedPullback f).map ((SingleComplexBaseChange.counit g).app H) ≫
      (SingleComplexBaseChange.counit f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map (β.hom.app H) := by
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
    have h := congrArg (fun t ↦ t.app H) hnat
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app] at h
    simp only [Category.id_comp] at h
    with_unfolding_all exact h
  have nc := (c f g).hom.naturality (pullbackTensorModelMap Z P N)
  dsimp only [Functor.comp_map] at nc
  have hr := congrArg
    (fun k ↦ (c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫ k)
    heq
  have hr' :
      ((c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫
        (mixedHomTensorPullbackIso (f ≫ g)).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
        (((SingleComplexBaseChange.counit (f ≫ g)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
          (SingleComplexBaseChange.counit (f ≫ g)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap X
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)) =
      (derivedPullback f).map ((derivedPullback g).map (pullbackTensorModelMap Z P N)) ≫
        (derivedPullback f).map ((SingleComplexBaseChange.counit g).app H) ≫
        (SingleComplexBaseChange.counit f).app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map (β.hom.app H) ≫ DerivedCategory.Q.map φ.hom := by
    calc
      _ = (c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫
          ((derivedPullback (f ≫ g)).map (pullbackTensorModelMap Z P N) ≫
            (SingleComplexBaseChange.counit (f ≫ g)).app H ≫
              DerivedCategory.Q.map φ.hom) := by
        exact (Category.assoc _ _ _).trans hr.symm
      _ = ((derivedPullback f).map
          ((derivedPullback g).map (pullbackTensorModelMap Z P N)) ≫
          (c f g).hom.app (DerivedCategory.Q.obj (pullbackTensorTotal Z P N))) ≫
            (SingleComplexBaseChange.counit (f ≫ g)).app H ≫
              DerivedCategory.Q.map φ.hom := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun k ↦ k ≫ (SingleComplexBaseChange.counit (f ≫ g)).app H ≫
            DerivedCategory.Q.map φ.hom) nc.symm)
      _ = _ := by rw [Category.assoc, reassoc_of% fac]
  exact hl.trans hr'.symm

end AlgebraicGeometry
