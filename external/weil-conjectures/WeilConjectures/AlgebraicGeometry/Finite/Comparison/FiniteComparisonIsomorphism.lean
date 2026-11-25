/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison

set_option linter.privateModule false

/-! # Invertibility of the specified finite tensor-unit comparison

Source: Stacks Project, Tags 03D2, 03D6 and 00WX; step 3 of
`lem-weil-point-automorphism-derived-transport-inverse`.
(blueprint: lem-weil-finite-comparison-complex-isomorphism)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]

private abbrev constantRing (W : AlgebraicGeometry.Scheme.{t})
    (A : CommRingCat.{max u (t + 1)}) :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj A)

private def finiteSectionwiseAdjunction (n : ℕ) :
    inverseImageFiniteModules l E g n ⊣ coefficientProEtaleModuleDirectImage g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max u (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let c := inverseImageFiniteCoefficientMap l E g n
  let φ := inv c
  let ψ : constantRing Y A ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj (constantRing X A) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap g A).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  have hc : (isoSectionwiseInverseImage g RingCat).map ψ ≫
      shAdj.counit.app (constantRing X A) = c := by
    apply (isoSectionwiseConstantMap_existsUnique g A).unique
    · intro U a
      have h := Equiv.apply_symm_apply ((sheafificationAdjunction (ProEt.topology Y)
        CommRingCat.{max u (t + 1)}).homEquiv
          ((Functor.const Y.ProEtᵒᵖ).obj A)
          (((proEtaleBaseChange g).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
            (ProEt.topology Y) (ProEt.topology X)).obj
              ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)))
        (Functor.whiskerLeft (proEtaleBaseChange g).op
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
      rw [Adjunction.homEquiv_unit] at h
      have hx := congrArg (fun k ↦ k.app (op ((proEtaleIsoPostcompose g).obj U)) a) h
      change ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
          (proEtaleIsoCommaArrow g U).op
          ((coefficientProEtaleDirectRingMap g A).hom.app _
            ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app _ a)) = _
      rw [show (coefficientProEtaleDirectRingMap g A).hom.app _
          ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app _ a) =
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app _ a from hx]
      exact (congrArg (fun k ↦ k a)
        ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
          (proEtaleIsoCommaArrow g U).op)).symm
    · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
  have hψ : ψ = shAdj.unit.app (constantRing Y A) ≫
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat _ _).map c := by
    change ψ = (shAdj.homEquiv _ _) c
    have hc' : (shAdj.homEquiv _ _).symm ψ = c := hc
    exact (Equiv.apply_symm_apply _ ψ).symm.trans
      (congrArg (shAdj.homEquiv _ _) hc')
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) (constantRing Y A).obj =
      ψ.hom ≫ (proEtaleBaseChange g).op.whiskerLeft φ.hom := by
    rw [hψ]
    ext U : 2
    simp [φ, shAdj, adj]
  have H₂ : φ.hom ≫ (proEtaleIsoPostcompose g).op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) (constantRing X A).obj =
        𝟙 (constantRing X A).obj := by
    have h : φ ≫ (isoSectionwiseInverseImage g RingCat).map ψ ≫
        shAdj.counit.app (constantRing X A) = 𝟙 _ := by
      rw [hc]
      exact IsIso.inv_hom_id c
    exact congrArg (fun f ↦ f.hom) h
  exact SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂

end AlgebraicGeometry.ProEtale
