/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechPinnedMate
import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Identification of the canonical map on the explicit alternating Čech model

Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Steps 2--5;
Stacks Project, Tags 02KH, 08HY, and 0A1D.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The module base-change composite factors through ordinary pullback of the
explicit Čech model, via a left-derived counit. No relative flatness is assumed
and no invertibility of that counit or of the composite is asserted.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Steps 2--5;
Stacks Project, Tags 02KH and 08HY.
(blueprint: lem-pc-affine-alternating-cech-base-change-factorization).

Proof: The increasing-tuple affine Čech resolution has a locally split augmented
complex: on a cover member insert its index, reorder, and use the sign of the
permutation, with repeated indices giving zero. Each intersection is affine and
its open pushforward is f_*-acyclic. The acyclic resolution comparison therefore
identifies Rf_*G with the sheafification of the A-section complex specified by
K = affineAlternatingCechModel f U G. Apply the same construction on the pulled
back cover. For every intersection the affine section-pullback formula gives
B tensor_A Gamma(G,U_J) = Gamma(p*G,p^-1(U_J)); finite products commute with tensor.
Its restriction-compatible pure-tensor formula intertwines the signed face maps,
so it yields the target identification t for ordinary pullback of K. Choose the
left-derived counit for g compatible with the derived adjunctions defining the
canonical mate. Evaluating the adjunction unit and counit on the Čech augmentation
shows that the canonical composite is Lg*(e) followed by this counit at K and t.
This is an equation of maps, checked by transposition under Lf_B* adjoint Rf_B*;
the triangle equations cancel the units and leave the ordinary section pullbacks.
For the given comparison c, compare its witnessing counit for p with this chosen
one using right Kan extension uniqueness. Derived tensor of G[0] is nonpositive
and its H0 is p*G. Maps to (p*G)[0] therefore factor uniquely through H0. The counit
automorphism induces an automorphism of p*G on H0; composing t with its derived
direct image gives the displayed equation for c as well. None of these steps uses
flatness over A or invertibility of the counit at K. Empty covers compute zero. -/
theorem affineAlternatingCech_baseChange_factorization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (c : (derivedPullback (pullback.fst f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))
    (hc : IsDerivedModulePullbackComparison (pullback.fst f g) G c) :
    ∃ (F : SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
      (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
      (_ : ∀ {M N} (a : M ⟶ N),
        F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
          eqToHom (hF N).symm)
      (_ : F.Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      (derivedPullback g).IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ (e : (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (affineAlternatingCechModel f U G)))
        (t : DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (affineAlternatingCechModel f U G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))),
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage (pullback.snd f g)).map c =
          (derivedPullback g).map e.hom ≫
            ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              (affineAlternatingCechModel f U G)) ≫ t.hom := by
  classical
  let a := fun {Y Z : Scheme.{u}} (k : Y ⟶ Z) ↦
    (Classical.choose exists_derivedPullbackComposition.{u, w}) k
  let := a g
  let := a (pullback.fst f g)
  let δ := fun {Y Z : Scheme.{u}} (k : Y ⟶ Z) ↦
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  let hδ := fun {Y Z : Scheme.{u}} (k : Y ⟶ Z) ↦
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) k
  let c₀ := (δ (pullback.fst f g)).app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback (pullback.fst f g))
        (ComplexShape.up ℤ) 0).hom.app G))
  have hc₀ : IsDerivedModulePullbackComparison (pullback.fst f g) G c₀ :=
    ⟨δ (pullback.fst f g), hδ (pullback.fst f g), rfl⟩
  obtain ⟨e, t, he⟩ := affineAlternatingCech_pinned_mate f g U hU haffine G
  simp only [cast_eq] at he
  obtain ⟨α, hα⟩ :=
    modulePullbackComparison_target_automorphism (pullback.fst f g) G c₀ c hc₀ hc
  refine ⟨Scheme.Modules.tensorPullback g, (fun _ ↦ rfl), ?_, inferInstance,
    δ g, hδ g, e,
    t ≪≫ (schemeDerivedDirectImage (pullback.snd f g)).mapIso
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).mapIso α), ?_⟩
  · intro M N b
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · rw [hα, Functor.map_comp, ← Category.assoc, he]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rfl

end AlgebraicGeometry
