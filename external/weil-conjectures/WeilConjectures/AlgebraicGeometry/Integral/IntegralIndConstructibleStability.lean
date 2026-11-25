/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Structural stability of integral ind-constructible cohomology
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u₁ u₂ u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem smallSupport
    {C : Type u₁} [Category.{v} C] [Preadditive C] [LocallySmall.{v} C]
    {I : Type u₂} (K : I → C) (t : Cofan K) (ht : IsColimit t) :
    Small.{v} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i =
      Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem closedUnderExistingCofan
    {C : Type u₁} [Category.{v} C] [Preadditive C] [LocallySmall.{v} C]
    (S : ObjectProperty C)
    (hsmall : ∀ (J : Type v) (K : J → C) (c : Cofan K),
      IsColimit c → (∀ j, S (K j)) → S c.pt)
    {I : Type u₂} (K : I → C) (hK : ∀ i, S (K i)) (t : Cofan K) (ht : IsColimit t) :
    S t.pt := by
  classical
  have := smallSupport K t ht
  let J := {i // ¬ IsZero (K i)}
  let U : J → C := fun i ↦ K i.val
  let r : Cofan U := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let e := (equivShrink.{v} J).symm
  let V : Shrink.{v} J → C := fun j ↦ U (e j)
  let r' : Cofan V := Cofan.mk t.pt (fun j ↦ r.inj (e j))
  have hr' : IsColimit r' := (Cofan.isColimitEquivOfEquiv e r) hr
  exact hsmall _ V r' hr' (fun j ↦ hK (e j).val)

/-- Integral ind-constructible cohomology is stable under upper truncation and
arbitrary ambient small coproducts and contains the localizing closure of Dbc.
There is no assumption about a proper map, a fibre dimension, or an Ext bound. -/
theorem integralIndConstructibleStability
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    let Λ := Profinite.padicIntegersRingObj ℓ E
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
    let S : ObjectProperty (DerivedCategory A) := fun K ↦ ∀ n : ℤ,
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor A n).obj K)
    (∀ K : DerivedCategory A, S K → ∀ a : ℤ,
      S ((DerivedCategory.TStructure.t.truncLE a).obj K)) ∧
    (∀ (I : Type (u + 1)) (K : I → DerivedCategory A), (∀ i, S (K i)) →
      ∀ c : Cofan K, IsColimit c → S c.pt) ∧
    (∀ K : DerivedCategory A, localizingClosure (constantModelBoundedConstructible Λ X) K →
      S K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let P := ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
  let S := DerivedCategory.homologyProperty P
  obtain ⟨hzero, hker, hcoker, hext, hsum⟩ :=
    integralIndConstructibleHeartClosure ℓ E k p₀ hp₀ hpℓ X
  let := hzero
  let := hker
  let := hcoker
  let := hext
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have : HasCoproducts.{u + 1} A := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have : HasCoproducts.{u + 1} (DerivedCategory A) := derived_hasCoproducts
  have hSsum (I : Type (u + 1)) (K : I → DerivedCategory A)
      (c : Cofan K) (hc : IsColimit c) (hK : ∀ i, S (K i)) : S c.pt := by
    intro n
    have ht := isColimitOfPreserves (DerivedCategory.homologyFunctor A n) hc
    exact hsum I (fun i ↦ (DerivedCategory.homologyFunctor A n).obj (K i))
      (Cofan.mk _ (fun i ↦ (DerivedCategory.homologyFunctor A n).map (c.inj i)))
      ((isColimitMapCoconeCofanMkEquiv _ _ _).1 ht) (fun i ↦ hK i n)
  refine ⟨fun K hK a ↦ DerivedCategory.homologyProperty_truncLE hK a,
    fun I K hK c hc ↦ hSsum I K c hc hK, ?_⟩
  have hSlocal : IsLocalizingSubcategory S := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG hGP
    let := hG
    let K : I → DerivedCategory A := fun i ↦ G.obj ⟨i⟩
    let e : G ≅ Discrete.functor K := Discrete.natIsoFunctor
    let c : Cofan K := (Cocone.precompose e.inv).obj (colimit.cocone G)
    have hc : IsColimit c := (IsColimit.precomposeInvEquiv e _).symm
      (colimit.isColimit G)
    exact closedUnderExistingCofan S hSsum K (fun i ↦ hGP i) c hc
  intro K hK
  exact hK S hSlocal (fun L hL n ↦ ObjectProperty.le_ind _ _ (hL.2 n))

end AlgebraicGeometry.ProEtale
