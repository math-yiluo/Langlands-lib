/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.PoincareDuality.ProjectionFormula
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Open extension by zero on localizing categories

The ambient categories are ordinary unbounded derived categories of module objects.
Constructibility uses finite constant models. The restricted functor is the canonical
full-subcategory lift of the existing termwise derived extension by zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint
  CondensedRing.openImmersionLowerShriek

private lemma finiteConstantLocalModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨𝒰, h𝒰⟩ := h
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩

private lemma constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  by_cases hX : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [IsConstantModelConstructible, ite_eq_left hX] at h ⊢
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · simp only [IsConstantModelConstructible, ite_eq_right hX] at h ⊢
    intro V hV
    obtain ⟨S, hS⟩ := h V hV
    exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso
        ((CondensedRing.upperStar Λ V.ι).mapIso e)) (hS a)⟩

private lemma finiteStratification_of_models {U : Scheme.{u}}
    (P : ∀ T : Scheme.{u}, (T ⟶ U) → Prop)
    (h : ∃ S : Scheme.Stratification U, ∀ a : Fin S.n, P (S.domain a) (S.immersion a)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification U,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ a : Fin S.n, P (S.domain a) (S.immersion a) := by
  obtain ⟨S, hS⟩ := h
  let S' : Scheme.FiniteLocallyClosedStratification U :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨S', S.isConstructible_stratum, hS⟩

private lemma openImmersionLowerShriek_bounded_degree
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (K : ConstantModelConstructibleFiniteTor Λ U) (n : ℤ) :
    IsConstantModelConstructible Λ X
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) := by
  have hpprime : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right
    (Nat.ne_of_gt _hp)⟩
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  let : QuasiSeparatedSpace U :=
    quasiSeparatedSpace_of_quasiSeparated (U ↘ Spec (.of k))
  have hU : CompactSpace U ∧ QuasiSeparatedSpace U := ⟨inferInstance, inferInstance⟩
  have hH := K.property.1.2 n
  rw [IsConstantModelConstructible, ite_eq_left hU] at hH
  obtain ⟨S, hcon, hS⟩ := finiteStratification_of_models
    (fun T f ↦ HasFiniteConstantLocalModel Λ T
      ((CondensedRing.upperStar Λ f).obj ((DerivedCategory.homologyFunctor _ n).obj K.obj))) hH
  have hc := (constantModelConstructible_openImmersionLowerShriek ℓ p _hpℓ k Λ j
    ((DerivedCategory.homologyFunctor _ n).obj K.obj) S hcon hS).1
  exact constantModelConstructible_of_iso Λ
    (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app
      K.obj) hc

private lemma openImmersionLowerShriek_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    ∀ K : ConstantModelConstructibleFiniteTor Λ U,
      constantModelBoundedConstructible Λ X
        ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj) := by
  intro K
  refine ⟨(CondensedRing.openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj
    K.property.1.1, ?_⟩
  intro n
  exact openImmersionLowerShriek_bounded_degree ℓ k p _hp _hpℓ Λ _hΛ j K n

private lemma openImmersionLowerShriek_tor
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    ∀ K : ConstantModelConstructibleFiniteTor Λ U,
      _root_.DerivedCategory.finiteTorAmplitude _
        ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj) := by
  intro K
  obtain ⟨a, b, hK⟩ := K.property.2
  refine ⟨a, b, fun M ↦ ?_⟩
  let M₀ := (DerivedCategory.singleFunctor _ 0).obj M
  let e := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
    Λ j).app M₀ ≪≫ ((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).app M
  have h := Functor.homologyConcentratedIn_mapDerivedCategory_obj
    (CondensedRing.openImmersionLowerShriek Λ j)
    (hK ((CondensedRing.upperStar Λ j).obj M))
  exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
    ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.mapIso
      (((curriedTensor _).obj K.obj).mapIso e).symm ≪≫
        asIso (CondensedRing.openImmersionProjectionComparison Λ j K.obj M₀)) h

private lemma openImmersionLowerShriek_generators
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    ∀ K : ConstantModelConstructibleFiniteTor Λ U,
      (constantModelBoundedConstructible Λ X ⊓ fun L ↦
        _root_.DerivedCategory.finiteTorAmplitude _ L)
          ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj) := by
  intro K
  exact ⟨openImmersionLowerShriek_bounded ℓ k p _hp _hpℓ Λ _hΛ j K,
    openImmersionLowerShriek_tor ℓ k p _hp _hpℓ Λ _hΛ j K⟩

/-- Open extension by zero preserves bounded constructible finite-Tor complexes and
all small direct sums, and restricts to an exact, sum-preserving functor on their
localizing closures. The existential triangulated structures below are the closure
properties needed for the inherited full-subcategory triangulations; the functor is
explicitly the canonical lift of `D(j_!)`, not an arbitrary functor. -/
theorem openImmersionLowerShriek_localizing
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ U,
      (constantModelBoundedConstructible Λ X ⊓ fun L ↦
        _root_.DerivedCategory.finiteTorAmplitude _ L)
          ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory) ∧
    ∃ (_ : (localizingClosureProEtale Λ U).IsTriangulated)
      (_ : (localizingClosureProEtale Λ X).IsTriangulated),
      ∃ h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
        localizingClosureProEtale Λ X
          ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj),
        ((localizingClosureProEtale Λ X).lift
          ((localizingClosureProEtale Λ U).ι ⋙
            (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory) h).IsTriangulated ∧
        ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
          ((localizingClosureProEtale Λ X).lift
            ((localizingClosureProEtale Λ U).ι ⋙
              (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory) h) := by
  have hsums : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory := by
    intro I
    infer_instance
  have hgenerators := openImmersionLowerShriek_generators ℓ k p _hp _hpℓ Λ _hΛ j
  refine ⟨hgenerators, hsums, ?_⟩
  let GU := constantModelBoundedConstructible Λ U ⊓ fun K ↦
    _root_.DerivedCategory.finiteTorAmplitude _ K
  let GX := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    _root_.DerivedCategory.finiteTorAmplitude _ K
  let J := (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory
  have hU := (localizingClosure_exists Λ U GU).2.2.2.1
  have hX := (localizingClosure_exists Λ X GX).2.2.2.1
  have hUt : (localizingClosureProEtale Λ U).IsTriangulated := hU.1
  have hXt : (localizingClosureProEtale Λ X).IsTriangulated := hX.1
  have hXi : (localizingClosureProEtale Λ X).IsClosedUnderIsomorphisms := hX.2.1
  have hmap : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ X (J.obj K.obj) := by
    intro K
    apply K.property ((localizingClosureProEtale Λ X).inverseImage J)
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hPD
      have := hD
      have : PreservesColimit D J :=
        (Adjunction.ofIsLeftAdjoint J).leftAdjoint_preservesColimits.preservesColimitsOfShape
          |>.preservesColimit
      have : HasColimit (D ⋙ J) := inferInstance
      exact (localizingClosureProEtale Λ X).prop_of_iso
        (preservesColimitIso J D).symm
        (hX.2.2 (D ⋙ J) inferInstance hPD)
    · intro L hL P hP hGP
      exact hGP _ (hgenerators ⟨L, hL⟩)
  refine ⟨hUt, hXt, hmap, inferInstance, ?_⟩
  intro I
  have closure_sums (T : Scheme.{u})
      (hT : IsLocalizingSubcategory (localizingClosureProEtale Λ T)) :
      (localizingClosureProEtale Λ T).IsClosedUnderColimitsOfShape (Discrete I) :=
    hT.isClosedUnderColimitsOfShape_discrete I
  have := closure_sums U hU
  have := closure_sums X hX
  have := (localizingClosure_exists Λ U GU).1
  have := (localizingClosure_exists Λ X GX).1
  have : PreservesColimitsOfShape (Discrete I)
      (((localizingClosureProEtale Λ X).lift
        ((localizingClosureProEtale Λ U).ι ⋙ J) hmap) ⋙
          (localizingClosureProEtale Λ X).ι) := by
    change PreservesColimitsOfShape (Discrete I) ((localizingClosureProEtale Λ U).ι ⋙ J)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (localizingClosureProEtale Λ X).ι

end AlgebraicGeometry.ProEtale
