/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenComparison

/-!
# FiniteNormalDepthTwoPurity

## References

* Stacks Project, Tags 0EYB, 0EY6 and 0EYJ (depth-two case)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem etale_restrict_sup {L N : Scheme.{u}} (n : N ⟶ L)
    (U W : L.Opens) (hU : Etale (n ∣_ U)) (hW : Etale (n ∣_ W)) :
    Etale (n ∣_ (U ⊔ W)) := by
  let T := U ⊔ W
  let J : Bool → L.Opens := fun b ↦ if b then U else W
  have hJ : ∀ b, J b ≤ T := by
    intro b
    cases b <;> simp [J, T]
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @Etale) (fun b ↦ T.ι ⁻¹ᵁ J b)
  · ext y
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
      Set.mem_preimage, Opens.ι_apply, SetLike.mem_coe, Bool.exists_bool,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact Or.symm y.property
  · intro b
    have hI : T.ι ''ᵁ (T.ι ⁻¹ᵁ J b) = J b := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (hJ b)
    have hEt : Etale (n ∣_ T.ι ''ᵁ (T.ι ⁻¹ᵁ J b)) := by
      rw [hI]
      cases b
      · simpa [J] using hW
      · simpa [J] using hU
    exact (MorphismProperty.arrow_mk_iso_iff @Etale
      (morphismRestrictRestrict n T (T.ι ⁻¹ᵁ J b))).mpr hEt

/-- Purity for finite normal covers in the indicated local-base case. -/
theorem finite_normal_etale_of_depth_two_neighbourhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    {L N : Scheme.{u}} (q : L ⟶ Spec (.of A))
    [QuasiCompact q] [QuasiSeparated q] [Smooth q] [GeometricallyConnected q]
    (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    (n : N ⟶ L) [IsFinite n]
    (hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (hdense : Dense (↑(n ⁻¹ᵁ (q ⁻¹ᵁ V)) : Set N))
    (het : Etale (n ∣_ (q ⁻¹ᵁ V)))
    (W : L.Opens) (x : L) (hx : x ∈ W)
    (hqx : q x = IsLocalRing.closedPoint A) (hW : Etale (n ∣_ W))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A) : Etale n := by
  let U := q ⁻¹ᵁ V
  let T := U ⊔ W
  have hnT : Etale (n ∣_ T) := etale_restrict_sup n U W het hW
  have haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ T := by
    intro y hy
    exact Or.inl ((hV (q y)).mpr hy)
  have hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ T) :
      Set (q.fiber (IsLocalRing.closedPoint A))) := by
    have : GeometricallyIrreducible q :=
      GeometricallyIrreducible.of_smooth_of_geometricallyConnected q
    apply ((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ T).isOpen.dense
    refine ⟨(q.fiberHomeo (IsLocalRing.closedPoint A)).symm ⟨x, hqx⟩, ?_⟩
    change q.fiberι _ _ ∈ T
    rw [q.fiberι_fiberHomeo_symm]
    exact Or.inr hx
  have : IsFinite (n ∣_ T) := inferInstance
  obtain ⟨E, p, hpfin, hpet, e, he⟩ :=
    exists_finite_etale_extension_of_local_depth_two A q T haway hclosed hdepth (n ∣_ T)
  have : IsFinite p := hpfin
  have : Etale p := hpet
  have : Nonempty L := ⟨x⟩
  have hA : ∀ y : Spec (.of A),
      IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk y) := by
    intro y
    have : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime y.asIdeal)
        y.asIdeal.primeCompl y.asIdeal.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv (StructureSheaf.stalkIso A y).toRingEquiv
  let S := Spec (.of A)
  let a := S.fromSpecStalk (genericPoint S)
  obtain ⟨hL, _, hnormalL, _⟩ := smooth_connected_generic_geometry_core hA q
    (pullback.fst a q) (pullback.snd a q) (IsPullback.of_hasPullback a q)
  have : IsIntegral L := hL
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  have hdenseT : Dense (↑(n ⁻¹ᵁ T) : Set N) :=
    hdense.mono (fun z hz ↦ Or.inl hz)
  have he' : e.inv ≫ p ∣_ T = n ∣_ T := by
    rw [← he]
    simp
  obtain ⟨i, hi⟩ := finite_normal_iso_of_dense_open_etale_comparison hnormalL n p
    hnormal T ⟨x, Or.inr hx⟩ hdenseT hnT e.symm he'
  rw [← hi]
  infer_instance

end AlgebraicGeometry.Scheme
