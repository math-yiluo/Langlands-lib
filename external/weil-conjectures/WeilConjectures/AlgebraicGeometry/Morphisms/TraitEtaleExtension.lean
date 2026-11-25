/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.SmoothNormalRing
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity

/-!
# Extending a punctured cover over a smooth trait

## References

* Stacks Project, Tags 0EYE and 0EYJ, trait paragraph
* Tag 033C for normality
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Smooth normality on affine charts, then localization to stalks (Stacks Tag 033C). -/
private theorem smooth_normal_stalks {S T : Scheme.{u}} (f : T ⟶ S) [Smooth f]
    (hS : ∀ y : S, IsDomain (S.presheaf.stalk y) ∧
      IsIntegrallyClosed (S.presheaf.stalk y)) :
    ∀ x : T, IsDomain (T.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.presheaf.stalk x) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU)
      (f ⁻¹ᵁ U).isOpen
  have hφ := f.smooth_appLE hU hV hVU
  have hnormal : ∀ (p : Ideal Γ(S, U)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    intro p hp
    let y : PrimeSpectrum Γ(S, U) := ⟨p, hp⟩
    have hy : hU.fromSpec y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact Set.mem_range_self y
    let := S.presheaf.algebra_section_stalk ⟨hU.fromSpec y, hy⟩
    have := hU.isLocalization_stalk' y hy
    obtain ⟨hd, hi⟩ := hS (hU.fromSpec y)
    let e := IsLocalization.algEquiv p.primeCompl
      (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)
    exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  let := T.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨hd, hi⟩ := hφ.isNormalRing hnormal P
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (T.presheaf.stalk x)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

/-- The nonfield puncture is a nonempty open of an integral spectrum; smooth maps
are open, so its inverse image is dense (Stacks Tag 01UA). -/
private theorem dense_puncture (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    (hA : ¬ IsField A) (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A)) [Smooth f] :
    Dense (↑(f ⁻¹ᵁ V) : Set T) := by
  have hne : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ≠ IsLocalRing.closedPoint A := by
    intro h
    have hm : IsLocalRing.maximalIdeal A = ⊥ := congrArg PrimeSpectrum.asIdeal h.symm
    exact hA (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
  have hd : Dense (V : Set (Spec (.of A))) :=
    V.isOpen.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, (hV _).mpr hne⟩
  exact hd.preimage f.isOpenMap

/-- The normal local dimension-one criterion, via Mathlib's DVR TFAE (Stacks Tag 00PD). -/
private theorem trait_isDVR (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : ¬ IsField A) (hdim : ringKrullDim A ≤ (1 : WithBot ℕ∞)) :
    IsDiscreteValuationRing A := by
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim
  apply ((IsDiscreteValuationRing.TFAE A hA).out 1 3).mpr
  have : Ring.DimensionLEOne A := ⟨fun hp hprime ↦ hprime.isMaximal_of_ne_bot hp⟩
  exact { (inferInstance : IsDomain A), (inferInstance : IsNoetherianRing A),
    (inferInstance : Ring.DimensionLEOne A), (inferInstance : IsIntegrallyClosed A) with }

/-- A punctured finite etale cover that has an etale model near a point of the
special fibre extends to a finite etale cover. No normality or density assumption
on the given model N is needed for this existence assertion. -/
theorem exists_finite_etale_extension_of_trait_neighbourhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    {L N : Scheme.{u}} (q : L ⟶ Spec (.of A))
    [QuasiCompact q] [QuasiSeparated q] [Smooth q] [GeometricallyConnected q]
    (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    (n : N ⟶ L) [IsFinite n]
    (het : Etale (n ∣_ (q ⁻¹ᵁ V)))
    (W : L.Opens) (x : L) (hx : x ∈ W)
    (hqx : q x = IsLocalRing.closedPoint A) (hW : Etale (n ∣_ W))
    (hdim : ringKrullDim A ≤ (1 : WithBot ℕ∞)) :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      (∀ z : E, IsDomain (E.presheaf.stalk z) ∧
        IsIntegrallyClosed (E.presheaf.stalk z)) ∧
      Dense (↑(p ⁻¹ᵁ (q ⁻¹ᵁ V)) : Set E) ∧
      ∃ e : (n ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ≅ (p ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme,
        e.hom ≫ (p ∣_ (q ⁻¹ᵁ V)) = n ∣_ (q ⁻¹ᵁ V) := by
  classical
  by_cases hA : IsField A
  · let : Field A := hA.toField
    have hVbot : V = ⊥ := by
      apply le_antisymm _ bot_le
      intro t ht
      exact False.elim ((hV t).mp ht (Subsingleton.elim _ _))
    subst V
    let E := (⊥ : L.Opens).toScheme
    let p : E ⟶ L := (⊥ : L.Opens).ι
    have : IsEmpty E := ⟨fun z ↦ z.2⟩
    refine ⟨E, p, inferInstance, inferInstance, ?_, ?_, ?_⟩
    · intro z
      exact isEmptyElim z
    · exact fun z ↦ isEmptyElim z
    · have : IsEmpty ((n ⁻¹ᵁ (q ⁻¹ᵁ ⊥)).toScheme) := by
        simpa only [Scheme.Hom.preimage_bot] using
          (show IsEmpty ((⊥ : N.Opens).toScheme) from ⟨fun z ↦ z.2⟩)
      have : IsEmpty ((p ⁻¹ᵁ (q ⁻¹ᵁ ⊥)).toScheme) := by
        simpa only [Scheme.Hom.preimage_bot] using
          (show IsEmpty ((⊥ : E.Opens).toScheme) from ⟨fun z ↦ z.2⟩)
      refine ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty, ?_⟩
      exact (isInitialOfIsEmpty).hom_ext _ _
  · have : IsDiscreteValuationRing A := trait_isDVR A hA hdim
    obtain ⟨E, p, hpfin, hpet, e, he⟩ :=
      exists_finite_etale_extension_of_dvr_neighbourhood A q V hV n het W x hx hqx hW
    have : Etale p := hpet
    have hnormal := smooth_normal_stalks (p ≫ q) (fun y ↦ by
      let : Algebra A ((Spec (.of A)).presheaf.stalk y) :=
        StructureSheaf.stalkAlgebra A y
      have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk y) y.asIdeal :=
        StructureSheaf.IsLocalization.to_stalk A y
      exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ y.asIdeal.primeCompl
        y.asIdeal.primeCompl_le_nonZeroDivisors⟩)
    refine ⟨E, p, hpfin, hpet, hnormal, ?_, e, he⟩
    simpa only [Scheme.Hom.comp_preimage] using dense_puncture A hA V hV (p ≫ q)

end AlgebraicGeometry.Scheme
