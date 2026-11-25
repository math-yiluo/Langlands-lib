/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateRootTensorPresentation
import WeilConjectures.CategoryTheory.Constant.ConstantScalarExplicitTensor
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonPureSections

/-! # Normalized finite Tate comparison maps

Source: Stacks Project, Tags 03PK, 03EK and 099R.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

attribute [local instance] Sheaf.monoidalCategory

-- Pin the existing coefficient-size instances to avoid an unconstrained maximum universe.
attribute [local instance 4000] WeilConjectures.sfAbSheafify
attribute [local instance 4000] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify
attribute [local instance 4000] WeilConjectures.sfAbBijective

attribute [-instance] integralCoefficientAbSheafify integralCoefficientRingSheafify
  integralCoefficientAbLocallyBijective in
private theorem first_comparison (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) :
    ∃ b : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA 1) ≅ finiteTateProSheaf l E n T 1,
      IsFiniteTateSiteComparison l E n T r hA 1 b := by
  let A := finiteTateCoefficient l E n
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : Finite A := inferInstance
  have hm : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hunit : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (r + 1)
  obtain ⟨sigma, d, hsections, hroot, htensor, hrest⟩ := finiteRootSiteComparison A
  obtain ⟨e, he⟩ := finite_tate_root_tensor_presentation l E n T hT r hA
  refine ⟨sigma _ hm hA T hunit ≪≫ e.symm, ?_⟩
  intro U W f a z x hx
  have hz : (ProEtale.cartierRootsIso T (l ^ (r + 1)) hm hunit).hom.hom.app W
      (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        (T.rootsOfUnitySheaf (l ^ (r + 1)))).obj.map f.op
          (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
            (T.rootsOfUnitySheaf (l ^ (r + 1)))).hom.app U (z 0))) =
      (limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app W
        (x 0) := by
    obtain ⟨v, hv, _⟩ := existsUnique_proEtaleRootsOfUnitySections T (l ^ (r + 1)) W
    have hinj : Function.Injective
        ((proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app W) := by
      intro s t h
      apply v.injective
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun y ↦ Additive.toMul y.down)
        ((hv s).trans (h.trans (hv t).symm))
    apply hinj
    apply ULift.ext
    exact congrArg Additive.ofMul
      ((hroot _ hm T hunit U W f (z 0)).trans (hx 0).symm)
  have hleft : Function.LeftInverse (e.inv.hom.app W) (e.hom.hom.app W) := by
    intro v
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun q ↦ q.hom) e.hom_inv_id) W) v
  apply hleft.injective
  change e.hom.hom.app W (e.inv.hom.app W
    ((sigma _ hm hA T hunit).hom.hom.app W _)) =
      e.hom.hom.app W (finiteTateProGenerator l E n T W a (x 0))
  have hi := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun q ↦ q.hom) e.inv_hom_id) W)
  change ∀ v, e.hom.hom.app W (e.inv.hom.app W v) = v at hi
  rw [hi]
  simp only [finiteTateEtalePowerGenerator]
  erw [htensor, hz, he]

/-- The finite root projection and the finite-root site comparison give normalized
comparison isomorphisms in every nonnegative degree.
Source: `lem-amb-finite-tate-site-descent`, proof steps 1 and 3; Stacks 03PK and 03EK
(blueprint: lem-amb-finite-tate-normalized-comparisons).

Proof: use `AmbTateRootProjectionData.theta` to identify the first pro-etale twist
with the scalar extension of the finite root module. Constant scalar restriction
identifies this extension with `finiteRootProTensor`; its pure sections are the
same tensors. Compose the finite-root site comparison with the inverse of this
identification. The root-unit formula and injectivity of the finite-root inclusion
prove the required normalization on arbitrary pro-etale tests. In degree zero use
the constant-module comparison. In degree k+2 tensor the comparisons for k+1 and 1,
using the monoidal comparison inverse image and constant scalar restriction. The
monoidal unit and tensor equations carry precisely the two recursively specified
pure generators to one another. This argument includes the empty scheme and
requires only annihilation of the coefficient ring by the stated positive power. -/
theorem finite_tate_normalized_comparisons :
    ∃ b : ∀ (T : Scheme.{u}), IsUnit (l : Γ(T, ⊤)) →
      ∀ (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k,
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      IsFiniteTateSiteComparison l E n T r hA k (b T hT r hA k)) := by
  classical
  have hall (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) :
      ∀ k : ℕ, ∃ b : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k,
        IsFiniteTateSiteComparison l E n T r hA k b := by
    let A := finiteTateCoefficient l E n
    let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
    let j := sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A)
    obtain ⟨e0, he0, heTensor⟩ :=
      ConstantScalarRestriction.explicit_tensor_comparisons (ProEt.topology T) A
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
      refine ⟨asIso (Functor.OplaxMonoidal.η F) ≪≫ e0, ?_⟩
      intro U W f a z x hx
      change e0.hom.hom.app W
        ((Functor.OplaxMonoidal.η F).hom.app W _) =
          (realizationRingUnit (ProEt.topology T) A).app W a
      simp only [finiteTateEtalePowerGenerator]
      erw [(comparison_pure_sections A T).2, he0]
    | one => exact first_comparison l E n T hT r hA
    | more k _ ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨c, hc⟩ := first_comparison l E n T hT r hA
      let M := finiteEtaleTateTwist T (l ^ (r + 1)) A hA (k + 1)
      let N := finiteEtaleTateLine T (l ^ (r + 1)) A hA
      obtain ⟨e, he⟩ := heTensor
        (coefficientTwistPower T (purTwistFiniteOne T l E n) (k + 1))
        (purTwistFiniteOne T l E n)
      refine ⟨asIso (Functor.OplaxMonoidal.δ F M N) ≪≫ tensorIso b c ≪≫ e, ?_⟩
      intro U W f a z x hx
      change e.hom.hom.app W
        ((b.hom ⊗ₘ c.hom).hom.app W
          ((Functor.OplaxMonoidal.δ F M N).hom.app W _)) = _
      simp only [finiteTateEtalePowerGenerator, finiteTateProPowerGenerator]
      erw [(comparison_pure_sections A T).1 M N]
      have hn := congr_app (Functor.LaxMonoidal.μ_natural j b.hom c.hom) W
      have hn' := ConcreteCategory.congr_hom hn
        ((((F.obj M).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U
            (finiteTateEtalePowerGenerator T A (l ^ (r + 1)) hA U a (k + 1)
              (fun i ↦ z i.castSucc))))) ⊗ₜ[A]
        (((F.obj N).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app N).hom.app U
            (finiteEtaleTateOneGenerator A (l ^ (r + 1)) T hA U 1
              (z (Fin.last (k + 1))))))))
      change (Functor.LaxMonoidal.μ j (finiteTateProSheaf l E n T (k + 1))
        (finiteTateProSheaf l E n T 1)).app W
        (b.hom.hom.app W _ ⊗ₜ[A] c.hom.hom.app W _) =
          (b.hom ⊗ₘ c.hom).hom.app W
            ((Functor.LaxMonoidal.μ j (F.obj M) (F.obj N)).app W _) at hn'
      erw [← hn']
      erw [hb U W f a (fun i ↦ z i.castSucc) (fun i ↦ x i.castSucc)
        (fun i ↦ hx i.castSucc)]
      have hc' := hc U W f 1 (fun _ ↦ z (Fin.last (k + 1)))
        (fun _ ↦ x (Fin.last (k + 1))) (fun _ ↦ hx (Fin.last (k + 1)))
      change c.hom.hom.app W _ =
        finiteTateProGenerator l E n T W 1 (x (Fin.last (k + 1))) at hc'
      erw [hc', he]
      rfl
  exact ⟨fun T hT r hA k ↦ (hall T hT r hA k).choose,
    fun T hT r hA k ↦ (hall T hT r hA k).choose_spec⟩

end AlgebraicGeometry.Scheme
