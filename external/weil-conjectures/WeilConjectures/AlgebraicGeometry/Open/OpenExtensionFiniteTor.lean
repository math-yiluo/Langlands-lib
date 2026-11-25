/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedFlatness
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Extension by zero preserves finite-Tor constructibility

The cohomological interval and the Tor interval are independent. The functor on
derived categories is the termwise descent of the recorded exact extension by zero.

## References

* Stacks, Tag 03DJ
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Termwise extension by zero at a positive finite coefficient stage, descended
along quasi-isomorphisms using its recorded exactness. The coefficient ring is the
recorded quotient by the chosen uniformizer, with its canonical finiteness witness. -/
noncomputable def finiteStageDerivedExtensionByZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E n)).mapDerivedCategory

private theorem realization_constructible_iff (X : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsConstructibleProEtaleModuleSheaf X A ((sfIntrinsicModuleEquivalence X A).functor.obj F) ↔
      ProEtale.IsConstructible (ULift.{u + 1, u} A) F := by
  obtain ⟨e⟩ := ProEtale.intrinsicRealization_restriction X A
  rw [proEtaleModuleRestriction_constructible_iff]
  exact ⟨fun h ↦ ProEtale.isConstructible_of_iso (e.app F) h,
    fun h ↦ ProEtale.isConstructible_of_iso (e.app F).symm h⟩

theorem extension_constructible {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules U (proEtaleConstantRing U A))
    (hF : IsConstructibleProEtaleModuleSheaf U A F) :
    IsConstructibleProEtaleModuleSheaf Y A ((sfIntrinsicExtensionByZero j A).obj F) := by
  let EU := sfIntrinsicModuleEquivalence U A
  have hf : ProEtale.IsConstructible (ULift.{u + 1, u} A) (EU.inverse.obj F) := by
    apply (realization_constructible_iff U A _).mp
    rw [proEtaleModuleRestriction_constructible_iff] at hF ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction U A).mapIso (EU.counitIso.app F).symm) hF
  obtain ⟨G, hG, ⟨e⟩⟩ :=
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ hf
  have := hG
  have := IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact j G
  apply (realization_constructible_iff Y A _).mpr
  exact ProEtale.isConstructible_of_iso
    ((ProEtale.openImmersionLowerShriekComparisonUpperStarIso _ j).app G ≪≫
      (ProEtale.openImmersionLowerShriek _ j).mapIso e)
    (ProEtale.isConstructible_comparisonUpperStar_obj _)

/-- Extension by zero preserves bounded constructibility, finite Tor amplitude,
every cohomological interval, and every Tor interval, independently. -/
theorem finiteStageDerivedExtensionByZero_constructibleFiniteTor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (j : U ⟶ Y) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of D.k))]
    (K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn U K)
    (hTor : HasFiniteProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E n) K) :
    WeilConjectures.finiteTorConstructible l E n hn Y
        ((finiteStageDerivedExtensionByZero l E n hn j).obj K) ∧
      (∀ c d : ℤ,
        (∀ r : ℤ, (r < c ∨ d < r) →
          IsZero ((DerivedCategory.homologyFunctor
            (proEtaleRingModules U
              (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj K)) →
        ∀ r : ℤ, (r < c ∨ d < r) →
          IsZero ((DerivedCategory.homologyFunctor
            (proEtaleRingModules Y
              (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) r).obj
                ((finiteStageDerivedExtensionByZero l E n hn j).obj K))) ∧
      (∀ a b : ℤ,
        HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E n) K a b →
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
          ((finiteStageDerivedExtensionByZero l E n hn j).obj K) a b) := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of D.k))
  let F := sfIntrinsicExtensionByZero j A
  have hvan (r : ℤ)
      (h : IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules U (proEtaleConstantRing U A)) r).obj K)) :
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) r).obj
          (F.mapDerivedCategory.obj K)) :=
    F.isZero_homologyFunctor_mapDerivedCategory_obj h
  have hc : intrinsicFiniteTorsionConstructible l E n hn Y
      (F.mapDerivedCategory.obj K) := by
    constructor
    · apply hK.1.subset
      intro r hr hz
      exact hr (hvan r hz)
    · intro r
      rw [proEtaleModuleRestriction_constructible_iff]
      exact ProEtale.isConstructible_of_iso
        ((proEtaleModuleRestriction Y A).mapIso
          ((F.mapDerivedCategoryHomologyFunctorIso r).app K))
        ((proEtaleModuleRestriction_constructible_iff Y A _).mp
          (extension_constructible j A _ (hK.2 r)))
  have ht : ∀ a b, HasProEtaleTorAmplitude U A K a b →
      HasProEtaleTorAmplitude Y A (F.mapDerivedCategory.obj K) a b := by
    intro a b hab
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
    have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
      intro hdiv
      exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
    have hk : IsUnit (l : D.k) := by
      simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
    let units (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
        ∀ x : T, Invertible (l : T.residueField x) := fun x ↦ by
      let φ : D.k →+* T.residueField x :=
        ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (T ↘ Spec (.of D.k)).appTop ≫
          T.Γevaluation x).hom
      exact (map_natCast φ l ▸ hk.map φ).invertible
    let := units U
    let := units Y
    obtain ⟨P, hf, hz, ⟨e⟩⟩ :=
      (finiteCoefficient_torAmplitude_iff_flatModel D l _hl E n hn U K hK a b hab.1).mp hab
    apply (finiteCoefficient_torAmplitude_iff_flatModel
      D l _hl E n hn Y _ hc a b hab.1).mpr
    refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj P, ?_, ?_, ?_⟩
    · intro q
      exact (AlgebraicGeometry.openClosedFlatness_proEtale A j j.closedComplement
        j.range_closedComplement (F.obj (P.X q))).2.1 (P.X q) (hf q)
    · intro q hq
      exact F.map_isZero (hz q hq)
    · exact ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P⟩
  refine ⟨⟨hc, ?_⟩, ?_, ht⟩
  · obtain ⟨a, b, hab⟩ := hTor
    exact ⟨a, b, ht a b hab⟩
  · intro c d h r hr
    exact hvan r (h r hr)

end AlgebraicGeometry.Scheme
