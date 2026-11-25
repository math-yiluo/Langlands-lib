/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
import all WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted

/-! # Semilinearity of the canonical finite reduction transitions

The explicit change-of-rings map retains its finite scalar action after restriction
to completed coefficients. Source: Stacks Tag 03EK
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u a b r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules.UnrestrictedTowerProof

variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
  (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
  (hf : ∀ N, F.obj N = changeOfRings f N)
  (hg : ∀ N, G.obj N = changeOfRings g N)

private theorem identifiedMap_smul (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : (F.obj M).val.obj U) :
    (identifiedMap f g q hq M F G hf hg).val.app U (s • x) =
      q.hom.app U s • (show (G.obj M).val.obj U from
        (identifiedMap f g q hq M F G hf hg).val.app U x) := by
  let a := (eqToHom (hf M)).val.app U
  let b := (sheafMap f g q hq M).val.app U
  let c := (eqToHom (hg M).symm).val.app U
  have hb : b (s • a x) = q.hom.app U s •
      (show (changeOfRings g M).val.obj U from b (a x)) := b.hom.map_smul s (a x)
  unfold identifiedMap restrictedMap
  change c (b (a (s • x))) = q.hom.app U s • c (b (a x))
  rw [map_smul, hb, map_smul]

end SheafOfModules.UnrestrictedTowerProof

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

attribute [local irreducible] SheafOfModules.UnrestrictedTowerProof.sheafMap
  completedIntegralCommRingProjectionUnrestricted
  completedIntegralCoefficientSheafUnrestricted

/-- Finite reduction transitions are semilinear for the finite coefficient reduction.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node).
Proof: identify the selected natural transformation with the termwise construction
by its unique pure-tensor characterization. The construction is restriction of an
actually linear map from the higher finite coefficient ring to the lower one. -/
theorem unrestrictedIntegralTransition_smul (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
    (U : Y.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj U)
    (x : (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i).val.obj U) :
    (((unrestrictedIntegralTransition l E Y n).app P).f i).val.app U (s • x) =
      (integralCoefficientSheafTransition l E Y n).hom.app U s •
        (show (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i).val.obj U from
          (((unrestrictedIntegralTransition l E Y n).app P).f i).val.app U x) := by
  let τ : unrestrictedIntegralComplexFunctor l E Y (n + 1) ⟶
      unrestrictedIntegralComplexFunctor l E Y n :=
    { app := fun Q ↦
        { f := fun j ↦ unrestrictedModuleStep l E Y n (Q.X j)
          comm' := fun j k _ ↦
            (unrestrictedModuleStep_naturality l E Y n (Q.d j k)).symm }
      naturality := fun Q Q' a ↦ by
        apply HomologicalComplex.hom_ext
        intro j
        exact unrestrictedModuleStep_naturality l E Y n (a.f j) }
  have hτ : τ = unrestrictedIntegralTransition l E Y n :=
    (unrestrictedIntegralTransition_existsUnique l E Y n).unique
      (fun Q j V a z ↦ unrestrictedModuleStep_tmul l E Y n (Q.X j) V a z)
      (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
  rw [← hτ]
  dsimp only [τ]
  unfold unrestrictedModuleStep
  exact SheafOfModules.UnrestrictedTowerProof.identifiedMap_smul
    (completedIntegralCommRingProjectionUnrestricted l E Y (n + 1))
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (unrestrictedCoefficientStep l E Y n) (unrestrictedCoefficientStep_comp l E Y n) (P.X i)
    (unrestrictedIntegralReductionFunctor l E Y (n + 1))
    (unrestrictedIntegralReductionFunctor l E Y n)
    (unrestrictedReduction_obj l E Y (n + 1)) (unrestrictedReduction_obj l E Y n) U s x

end WeilConjectures
