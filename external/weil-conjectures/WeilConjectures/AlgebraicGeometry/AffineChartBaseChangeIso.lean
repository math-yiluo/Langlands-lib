/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Spectrum presentation of the base change of one affine chart

Source: Stacks Project, Schemes, Tags 01JR and 01I4.
(blueprint: lem-weil-pbc-affine-chart-base-change-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A specified spectrum presentation of an open chart over an affine base induces a
spectrum presentation of its inverse image under base change, with both projections fixed.

Source: Stacks Project, Schemes, Tags 01JR (open fibre products) and 01I4
(affine fibre products).
(blueprint: lem-weil-pbc-affine-chart-base-change-iso).

Proof: Form the pullback of Spec(B) and Spec(A) over Spec(R), and map it to
Z ×[S] T using eB.inv followed by V.ι, e.inv followed by (t ⁻¹ᵁ W).ι,
and e0.inv followed by W.ι. The two compatibility equations make this a map of
pullback diagrams. All three vertical maps are open immersions; hence the induced
map is an open immersion. Its image is the intersection of the inverse images of
V and t⁻¹(W). Since V maps into W, the first inverse image is already contained
in the second, by the pullback equation. Thus its image equals the inverse image
of V. The open immersion is therefore isomorphic to that open subscheme.
Compose this isomorphism with the symmetry of the affine fibre product and
pullbackSpecIso R A B. The inverse has the stated projections by the defining
projection equations of pullback.map and pullbackSpecIso. This works also when
V or t⁻¹(W) is empty, since spectra and fibre products allow zero rings. -/
theorem exists_affineChart_baseChangeIso
    {S Z : Scheme.{u}} (z : Z ⟶ S)
    (W : S.Opens) (V : Z.Opens) (eV : V ≤ z ⁻¹ᵁ W)
    (R B : CommRingCat.{u}) [Algebra R B]
    (e0 : W.toScheme ≅ Spec R) (eB : V.toScheme ≅ Spec B)
    (hB : z.resLE W V eV ≫ e0.hom =
      eB.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (T : Scheme.{u}) (t : T ⟶ S) (A : CommRingCat.{u}) [Algebra R A]
    (e : (t ⁻¹ᵁ W).toScheme ≅ Spec A)
    (h : t.resLE W _ le_rfl ≫ e0.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ i : ((pullback.fst z t) ⁻¹ᵁ V).toScheme ≅ Spec (.of (A ⊗[R] B)),
      i.inv ≫ ((pullback.fst z t) ⁻¹ᵁ V).ι ≫ pullback.fst z t =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
          eB.inv ≫ V.ι ∧
      i.inv ≫ ((pullback.fst z t) ⁻¹ᵁ V).ι ≫ pullback.snd z t =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
          e.inv ≫ (t ⁻¹ᵁ W).ι  := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let kB := eB.inv ≫ V.ι
  let kA := e.inv ≫ (t ⁻¹ᵁ W).ι
  let kR := e0.inv ≫ W.ι
  have hb : b ≫ kR = kB ≫ z := by
    dsimp [b, kR, kB]
    rw [← cancel_epi eB.hom]
    simp only [← Category.assoc, ← hB]
    simp
  have ha : a ≫ kR = kA ≫ t := by
    dsimp [a, kR, kA]
    rw [← cancel_epi e.hom]
    simp only [← Category.assoc, ← h]
    simp
  let m := pullback.map b a z t kB kA kR hb ha
  have : IsOpenImmersion m :=
    Scheme.pullback_map_isOpenImmersion b a z t kB kA kR hb ha
  have hrB : Set.range kB = V := by
    simp only [kB, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have hs : Function.Surjective eB.inv := fun x ↦
      ⟨eB.hom x, by change (eB.hom ≫ eB.inv) x = x; simp⟩
    rw [Set.range_eq_univ.mpr hs, Set.image_univ]
    exact Scheme.Opens.range_ι V
  have hrA : Set.range kA = t ⁻¹ᵁ W := by
    simp only [kA, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have hs : Function.Surjective e.inv := fun x ↦
      ⟨e.hom x, by change (e.hom ≫ e.inv) x = x; simp⟩
    rw [Set.range_eq_univ.mpr hs, Set.image_univ]
    exact Scheme.Opens.range_ι _
  have hsub : (pullback.fst z t) ⁻¹ᵁ V ≤ (pullback.snd z t) ⁻¹ᵁ (t ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
    exact ((TopologicalSpace.Opens.map (pullback.fst z t).base).map (homOfLE eV)).le
  have hr : Set.range m = Set.range (((pullback.fst z t) ⁻¹ᵁ V).ι) := by
    rw [Scheme.Opens.range_ι]
    dsimp [m]
    rw [Scheme.Pullback.range_map]
    change (pullback.fst z t ⁻¹' Set.range kB) ∩
      (pullback.snd z t ⁻¹' Set.range kA) = _
    rw [hrB, hrA]
    exact Set.inter_eq_left.mpr hsub
  let d := IsOpenImmersion.isoOfRangeEq m (((pullback.fst z t) ⁻¹ᵁ V).ι) hr
  let i := d.symm ≪≫ pullbackSymmetry b a ≪≫ pullbackSpecIso R A B
  refine ⟨i, ?_, ?_⟩
  · dsimp [i]
    simp only [Category.assoc]
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    dsimp [m]
    rw [pullback.lift_fst, pullbackSymmetry_inv_comp_fst_assoc,
      pullbackSpecIso_inv_snd_assoc]
  · dsimp [i]
    simp only [Category.assoc]
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    dsimp [m]
    rw [pullback.lift_snd, pullbackSymmetry_inv_comp_snd_assoc,
      pullbackSpecIso_inv_fst_assoc]

end AlgebraicGeometry
