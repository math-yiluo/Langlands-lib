/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.SmoothNormalRing

/-! # Smooth geometrically connected families over a normal integral base

## References

* Stacks Project, Tags 034F, 056T and 01UA
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A nonempty smooth geometrically connected family over a normal integral base
has normal integral total space and generic fibre. -/
theorem smooth_connected_generic_geometry_core {S C : Scheme.{u}} [IsIntegral S]
    [Nonempty C] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c) :
    ∃ hC : IsIntegral C, letI := hC;
      ∃ hη : IsIntegral Cη, letI := hη;
        (∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) ∧
        (∀ x : Cη, IsIntegrallyClosed (Cη.presheaf.stalk x)) := by
  have : GeometricallyIrreducible c :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected c
  have : IrreducibleSpace C := GeometricallyIrreducible.irreducibleSpace c c.isOpenMap
  have : GeometricallyReduced c := Smooth.geometricallyReduced c
  have : Finite (irreducibleComponents S) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have : IsReduced C :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents c
  have hC : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  have : Smooth q := MorphismProperty.of_isPullback hCη.flip ‹Smooth c›
  have : ConnectedSpace Cη :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hCη.flip
  have : IsLocallyNoetherian Cη := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsRegular Cη := IsRegular.of_smooth q
  have hη : IsIntegral Cη := IsRegular.isIntegral Cη
  refine ⟨hC, hη, ?_, ?_⟩
  · intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (c x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      C.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ c ⁻¹ᵁ U from hxU)
        (c ⁻¹ᵁ U).isOpen
    have hφ := HasRingHomProperty.appLE @Smooth c ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
    have hnormal : ∀ (p : Ideal Γ(S, U)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
      intro p hp
      let y : PrimeSpectrum Γ(S, U) := ⟨p, hp⟩
      have hy : hU.fromSpec y ∈ U := by
        rw [← SetLike.mem_coe, ← hU.range_fromSpec]
        exact Set.mem_range_self y
      let := S.presheaf.algebra_section_stalk ⟨hU.fromSpec y, hy⟩
      have := hU.isLocalization_stalk' y hy
      have := hS (hU.fromSpec y)
      let e := IsLocalization.algEquiv p.primeCompl
        (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)
      exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
    let := C.presheaf.algebra_section_stalk ⟨x, hxV⟩
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    let P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    have := (hφ.isNormalRing hnormal P).2
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
        (C.presheaf.stalk x)).toRingEquiv
  · intro x
    have := IsRegular.uniqueFactorizationMonoid_stalk x
    infer_instance

end AlgebraicGeometry.Scheme
