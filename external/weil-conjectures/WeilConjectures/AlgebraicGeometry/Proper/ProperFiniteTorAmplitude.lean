/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperBoundedConstructible
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Proper direct image preserves finite Tor amplitude

Membership in `Dctf` with a specified Tor interval is expressed by bounded
constructibility together with `hasTorAmplitudeIn` for that interval. This already
includes finite Tor amplitude, both in the hypothesis and in the conclusion.

## References

* Stacks Project, Tags 0F0G and 0F12
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Proper direct image preserves bounded constructible complexes of finite Tor amplitude,
with upper Tor bound increased by a bound for the geometric fibres' ℓ-cohomological dimensions. -/
theorem isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper
    (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0)
    (d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
      (F : Sheaf (pullback f y).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (U : (pullback f y).Etale) (s : F.obj.obj (op U)),
        ∃ n : ℕ, (ℓ ^ n) • s = 0) →
      ∀ i : ℤ, (d : ℤ) < i →
        IsZero ((cohomology AddCommGrpCat.{u + 1} (pullback f y) i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
    (a b : ℤ) (hab : a ≤ b) (C : DerivedCategoryModule A X)
    (hC : DerivedCategory.isBoundedConstructible A X C)
    (hCab : DerivedCategory.hasTorAmplitudeIn A X a b C) :
    DerivedCategory.isBoundedConstructible A Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj C) ∧
    DerivedCategory.hasTorAmplitudeIn A Y a (b + (d : ℤ))
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj C) := by
  classical
  have _ := hp
  have _ := hab
  obtain ⟨r, hr, hAr⟩ := hA
  have hAr' : (ℓ ^ r : A) = 0 := by simpa using hAr
  have hchar : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k hℓ hpℓ
  have hcoeff (T : Scheme.{u}) (t : T ⟶ Spec (.of k)) :
      IsSmoothBaseChangeCoefficients (ℓ ^ r) A T := by
    refine ⟨pow_pos hℓ.pos r, inferInstance, by simpa using hAr', ?_⟩
    have hu : IsUnit (ℓ ^ r : Γ(Spec (.of k), ⊤)) := by
      simpa using (hchar.isUnit.pow r).map (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa using hu.map t.appTop.hom
  refine ⟨isBoundedConstructible_rightDerivedLowerStar_of_proper A (ℓ ^ r)
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) f (by simp)
    (hcoeff X (X ↘ Spec (.of k))) (hcoeff Y (Y ↘ Spec (.of k))) C hC, ?_⟩
  have hdim : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℕ), d < q → IsZero (((lowerStar (ModuleCat.{u + 1} A) f).rightDerived q).obj F) := by
    intro F q hq
    have hfiber (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ Y)
        (G : Sheaf (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} A)) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) (pullback.snd f y)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
      let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
      let S := sheafCompose (pullback f y).smallEtaleTopology U
      have htors : ∀ (V : (pullback f y).Etale) (s : (S.obj G).obj.obj (op V)),
          ∃ n : ℕ, (ℓ ^ n) • s = 0 := by
        intro V s
        refine ⟨r, ?_⟩
        let s' : G.obj.obj (op V) := s
        change (ℓ ^ r) • s' = 0
        rw [← one_smul A s', ← smul_assoc, hAr, zero_smul]
      have hab := hd Ω y (S.obj G) htors (q : ℤ) (by exact_mod_cast hq)
      obtain ⟨eforget⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso (pullback f y) A q
      have hmod : IsZero ((cohomology (ModuleCat.{u + 1} A) (pullback f y) (q : ℤ)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
        have hz : IsZero (U.obj
            ((cohomology (ModuleCat.{u + 1} A) (pullback f y) (q : ℤ)).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
          hab.of_iso (eforget.app G)
        rw [IsZero.iff_id_eq_zero] at hz ⊢
        exact U.map_injective (by simpa using hz)
      let Γ := Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} A)
      let : ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence :=
        ((Scheme.geometricPoint_pullback_stalk Ω).2.2.2.1 A).1
      let : Γ.IsEquivalence := Functor.isEquivalence_of_iso
        (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
          (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _)).symm
      let E := (_root_.DerivedCategory.singleFunctor _ 0).obj G
      let L := (rightDerivedLowerStar (ModuleCat.{u + 1} A) (pullback.snd f y)).obj E
      let e := Γ.rightDerivedFunctorIsoMapDerivedCategory.symm.app L ≪≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} A) (pullback.snd f y)).app E
      exact Γ.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (hmod.of_iso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso e))
    refine isZero_of_forall_isZero_upperStar_algClosurePoint A _ fun t ↦ ?_
    let x := Y.algClosurePoint t
    let sq := IsPullback.of_hasPullback f x
    have := isIso_baseChange_of_isProper_of_isAddTorsion_ring A
      (fun z ↦ isOfFinAddOrder_of_finite z) sq
    rw [baseChange_eq_derivedBaseChangeMapPlus] at this
    let G := (upperStar (ModuleCat.{u + 1} A) (pullback.fst f x)).obj F
    have hvan := hfiber _ x G
    let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
    let v := lowerStar (ModuleCat.{u + 1} A) f
    let v' := lowerStar (ModuleCat.{u + 1} A) (pullback.snd f x)
    let u := upperStar (ModuleCat.{u + 1} A) x
    let u' := upperStar (ModuleCat.{u + 1} A) (pullback.fst f x)
    refine IsZero.of_iso hvan
      (u.mapIso (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm ≪≫
        (u.mapDerivedCategoryPlusHomologyFunctorIso q).app
          (v.rightDerivedFunctorPlus.obj K) ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app K)) ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (v'.rightDerivedFunctorPlus.mapIso
            ((u'.mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
        v'.homologyRightDerivedFunctorPlusObjSingleFunctorIso G q ≪≫
        (v'.homologyRightDerivedFunctorObjSingleFunctorIso G q).symm)
  intro M q hq
  let B := ((derivedTensor (ModuleCat.{u + 1} A) X).obj C).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((upperStar (ModuleCat.{u + 1} A) f).obj M))
  have hB : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj B) :=
    hCab ((upperStar (ModuleCat.{u + 1} A) f).obj M)
  have : B.IsGE a := (_root_.DerivedCategory.isGE_iff B a).2
    (fun i hi ↦ hB i (Or.inl hi))
  have : B.IsLE b := (_root_.DerivedCategory.isLE_iff B b).2
    (fun i hi ↦ hB i (Or.inr hi))
  have hlo : ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj B).IsGE a :=
    Functor.isGE_rightDerivedFunctor_obj _ _ _
  have hhi : ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj B).IsLE
      (b + (d : ℤ)) :=
    Functor.isLE_rightDerivedFunctor_obj_of_dimension _ d hdim B b inferInstance
  have hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj B)) := by
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 hlo q hq
    · exact (_root_.DerivedCategory.isLE_iff _ (b + (d : ℤ))).1 hhi q hq
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A f
  let e := asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app C).app
    ((_root_.DerivedCategory.singleFunctor _ 0).obj M))
  let e' := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app M
  exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (e ≪≫ (rightDerivedLowerStar (ModuleCat.{u + 1} A) f).mapIso
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj C).mapIso e')))

end AlgebraicGeometry.Etale
