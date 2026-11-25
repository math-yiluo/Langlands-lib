/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionIsIso
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence

/-!
# Composition and coherence of derived pullbacks

Source: Stacks Project, Cohomology, Lemma 20.27.2, Tag 0D5S
(blueprint: lem-pc-ringed-spaces-derived-pullback-composition).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private theorem tensorDerivedCounit {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))] :
    ∃ (_ : (Scheme.Modules.tensorPullback f).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh
            (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      derivedPullback_spec f
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

/-- The canonical composition comparisons `c f g : Lf^* ∘ Lg^* ≅ L(g ∘ f)^*` of derived
pullbacks, together with identity comparisons `i X : L(id_X)^* ≅ id`, both unit laws and
associativity. The comparison is tied to the left-derived universal property: `ε f` is a
left-derived counit of `derivedPullback f` for the recorded tensor pullback, and `c f g` is
the morphism into the left derived functor `derivedPullback (f ≫ g)` induced by the counits
of `g` and `f` followed by the canonical underived identification
`tensorPullback g ⋙ tensorPullback f ≅ tensorPullback (f ≫ g)`, the conjugate of
`pushforwardComp f g` under the pinned tensor-pullback adjunctions.
The family of derived-category instances only chooses the localizations; it imposes no
geometric condition on the schemes or morphisms.
Source: Stacks Project, Cohomology, Tag 0D5S
(blueprint: lem-pc-ringed-spaces-derived-pullback-composition).
Proof, step 1: choose a K-flat resolution on Z (lem-pc-kflat-resolution). Pullback
preserves K-flatness (lem-pc-kflat-pullback-preservation), so successive derived
pullbacks are represented by successive termwise tensor pullbacks
(lemma-coherent-base-change-invertible-sheaves--2): the counits at a K-flat complex and at its
pullback are invertible. The canonical underived identification then makes the induced morphism into
`L(g ∘ f)^*` invertible, natural in the complex.
Step 2: identity pullback is the tensor unitor. On a K-flat representative the two
unit laws are the tensor unit laws, and the two triple-composition paths are the two
reassociations of the same tensor expression; tensor associativity makes them equal.
Uniqueness of morphisms into a left derived functor descends these laws to the derived
categories. -/
theorem exists_derivedPullbackComposition
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))] :
    ∃ (_ : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (_ : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))),
    ∃ c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g),
      (∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
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
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))))) ∧
      ∃ i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _,
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c (𝟙 X) f ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.id_comp f)) =
            Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫
              Functor.rightUnitor (derivedPullback f)) ∧
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c f (𝟙 Y) ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.comp_id f)) =
            Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫
              Functor.leftUnitor (derivedPullback f)) ∧
        (∀ {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
          Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
            Functor.associator (derivedPullback g) (derivedPullback f)
                (derivedPullback h) ≪≫
              Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
                eqToIso (congrArg (fun k : W ⟶ Z => derivedPullback k)
                  (Category.assoc h f g))) := by
  classical
  let a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
      (Scheme.Modules.tensorPullback f).Additive := fun f ↦
    Classical.choose (tensorDerivedCounit f)
  let ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
      DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) :=
    fun f ↦ Classical.choose (Classical.choose_spec (tensorDerivedCounit f))
  have hL := fun {X Y : Scheme.{u₁}} (f : X ⟶ Y) ↦
    (Classical.choose_spec (Classical.choose_spec (tensorDerivedCounit f))).1
  have hK := fun {X Y : Scheme.{u₁}} (f : X ⟶ Y) ↦
    (Classical.choose_spec (Classical.choose_spec (tensorDerivedCounit f))).2
  let c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) := fun {X Y Z} f g ↦ by
    have := isIso_derivedPullbackCompositionLift a ε hL hK f g
    exact asIso ((derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
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
  refine ⟨a, ε, hL, c, ?_, ?_⟩
  · intro X Y Z f g
    rfl
  · exact derivedPullbackComposition_coherence a ε hL hK c (fun _ _ ↦ rfl)

end AlgebraicGeometry
