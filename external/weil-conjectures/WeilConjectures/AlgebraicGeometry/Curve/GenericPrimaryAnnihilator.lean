/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.FieldTheory.OpenSubgroupFixedField
import WeilConjectures.RepresentationTheory.SylowModuleFiltration
/-!
# A uniform annihilator from a finite primary geometric stalk

Source: blueprint `theorem-cohomology-curves--2`, proof paragraphs 1--2.
(blueprint: lem-sc-generic-primary-annihilator)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace AlgebraicGeometry.IsConnectedCurve
/-- A finite primary geometric stalk yields an ell-power annihilator.
Source: blueprint `theorem-cohomology-curves--2`, proof paragraphs 1--2.
Proof: the finite primary stalk has a largest exponent among the exponents
needed to kill its elements. The stalk functor is faithful on this site, so
the corresponding scalar multiple of the identity of `M` is zero.
(blueprint: lem-sc-generic-primary-annihilator) -/
theorem exists_primary_annihilator
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ℓ : ℕ)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup ℓ (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (e : ℕ), (ℓ ^ e) • 𝟙 M = 0 := by
  let s := Spec.map (CommRingCat.ofHom
    (algebraMap C.functionField (AlgebraicClosure C.functionField)))
  let Φ := Scheme.pointSmallEtale s
  let : Finite ((Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).obj M) := hfinite
  obtain ⟨e, he⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hprimary
  have hkill (x : (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).obj M) : (ℓ ^ e) • x = 0 := by
    simpa using congrArg Multiplicative.toAdd (he (Multiplicative.ofAdd x))
  have hmap : Φ.sheafFiber.map ((ℓ ^ e) • 𝟙 M) = Φ.sheafFiber.map (0 : M ⟶ M) := by
    rw [Φ.sheafFiber_map_smul, CategoryTheory.Functor.map_id]
    ext x
    simpa using hkill x
  refine ⟨e, ?_⟩
  have hs : ⋃ _ : PUnit.{u + 1}, Set.range s = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨PUnit.unit, default, Subsingleton.elim _ _⟩
  have hc := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec C.functionField) (fun _ : PUnit.{u + 1} ↦ s) hs
  refine (hc.jointlyFaithful AddCommGrpCat.{u + 1}).map_injective ?_
  rintro ⟨-, ⟨i⟩⟩
  -- Compare with the universe-lifted point used by the conservative-family theorem.
  have iso := Φ.uliftSheafFiberIso.{u + 1} AddCommGrpCat.{u + 1}
  rw [← Iso.cancel_iso_hom_right _ _ (iso.app M), Iso.app_hom,
    iso.hom.naturality, iso.hom.naturality, hmap]
end AlgebraicGeometry.IsConnectedCurve
