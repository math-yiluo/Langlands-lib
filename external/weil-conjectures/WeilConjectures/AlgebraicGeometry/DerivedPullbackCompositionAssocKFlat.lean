/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackHomotopyCompAssoc

/-! Associativity calculation on K-flat representatives for derived pullback. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

/-- The two triple-composition paths have equal components on a K-flat complex.
Source: Stacks Project, Cohomology, Tag 0D5S, Lemma 20.27.2;
Mathlib `Adjunction.leftAdjointCompIso_assoc`.
(blueprint: lem-pc-derived-pullback-assoc-kflat).
Proof: let H be the homotopy image of P. Tensor pullback by g, and then by f,
preserves K-flatness (lem-pc-kflat-pullback-preservation). Thus hK makes the
successive counits invertible, both at H and at its tensor pullbacks. Evaluate
hc for (f,g), (h,f), (h,f≫g), and (h≫f,g) and use leftDerived_fac_app.
Postcompose each of the proposed paths with the counit of h≫f≫g at H.
Naturality moves each counit past the preceding comparison; associators of
functors have identity components. After these rewrites each side is the
same ordered sequence: the counit of g at H, the counit of f at its tensor
pullback, the counit of h at the second tensor pullback, and then the
underived triple tensor comparison mapped by Qh. The two underived comparisons
are equal by leftAdjointCompIso_assoc applied to the pinned adjunctions and
the pushforward associativity law. Transport along Category.assoc carries
the adjunction for the composite to the same pinned adjunction; thus the
mate calculation includes precisely the eqToIso in the displayed formula.
Cancel the invertible final counit hK (h≫f≫g) P hP. This gives the component
equality, without resolving any other complex or asserting global coherence.
The calculation works for zero complexes, empty schemes, and identity morphisms. -/
theorem derivedPullbackComposition_assoc_kflat
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (hL : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hK : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y)
      (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ),
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        IsIso ((ε f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    (c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
    (hc :∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (c f g).hom =
          (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))))
    {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Z.sheaf) P) :
    (Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g)).hom.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    (Functor.associator (derivedPullback g) (derivedPullback f)
        (derivedPullback h) ≪≫
      Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
        eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
          (Category.assoc h f g))).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  let q := (HomotopyCategory.quotient
    (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)).obj P
  let m := (ε (h ≫ f ≫ g)).app q
  let _ := hK (h ≫ f ≫ g) P hP
  apply (cancel_mono m).1
  let _ := @hL
  let T {X Y : Scheme.{u₁}} (f : X ⟶ Y) :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
  let t {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (ComplexShape.up ℤ)
  have fac {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (H : HomotopyCategory (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace))
        (ComplexShape.up ℤ)) :
      (c f g).hom.app (DerivedCategory.Qh.obj H) ≫ (ε (f ≫ g)).app H =
        (derivedPullback f).map ((ε g).app H) ≫ (ε f).app ((T g).obj H) ≫
          DerivedCategory.Qh.map ((t f g).hom.app H) := by
    rw [hc]
    simp [T, t]
  let H := (HomotopyCategory.quotient
    (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)).obj P
  simp only [Category.assoc, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, eqToIso_refl,
    Iso.refl_hom, Category.id_comp, Category.comp_id]
  change (derivedPullback h).map ((c f g).hom.app (DerivedCategory.Qh.obj H)) ≫
      (c h (f ≫ g)).hom.app (DerivedCategory.Qh.obj H) ≫ (ε (h ≫ f ≫ g)).app H =
    (c h f).hom.app ((derivedPullback g).obj (DerivedCategory.Qh.obj H)) ≫
      (c (h ≫ f) g).hom.app (DerivedCategory.Qh.obj H) ≫ (ε (h ≫ f ≫ g)).app H
  rw [fac h (f ≫ g) H]
  have fac2 := fac (h ≫ f) g H
  change (c (h ≫ f) g).hom.app (DerivedCategory.Qh.obj H) ≫
      (ε (h ≫ f ≫ g)).app H =
    (derivedPullback (h ≫ f)).map ((ε g).app H) ≫
      (ε (h ≫ f)).app ((T g).obj H) ≫
        DerivedCategory.Qh.map ((t (h ≫ f) g).hom.app H) at fac2
  rw [fac2]
  rw [← Functor.map_comp_assoc, fac f g H]
  have nc := (c h f).hom.naturality ((ε g).app H)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nc
  rw [← reassoc_of% nc, reassoc_of% (fac h f ((T g).obj H))]
  simp only [Functor.map_comp, Category.assoc]
  have ne := (ε h).naturality ((t f g).hom.app H)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ne
  rw [reassoc_of% ne]
  have ht := tensorPullback_homotopy_comp_assoc a h f g H
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun k ↦ (derivedPullback h).map ((derivedPullback f).map ((ε g).app H)) ≫
      (derivedPullback h).map ((ε f).app ((T g).obj H)) ≫
      (ε h).app ((T f).obj ((T g).obj H)) ≫ DerivedCategory.Qh.map k) ht

end AlgebraicGeometry
