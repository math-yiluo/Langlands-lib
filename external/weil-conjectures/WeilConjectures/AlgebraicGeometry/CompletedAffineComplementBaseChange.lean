/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # The complement of an extended ideal under affine completion base change

Source: Stacks Project, Tag 088B, the construction of the completed-base projection.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An isomorphism over the complement of K stays an isomorphism over the complement
of the extended affine ideal after completion base change.

Source: Stacks Project, Tag 088B, paragraph defining Y', X' and the pullback of K;
stability of isomorphisms under base change.
(blueprint: lem-weil-pbc-completed-affine-complement-base-change)

Proof: Let g be the completion map followed by the inverse affine chart and the
inclusion of U. On U the support of K is the zero locus of K(U). Under the affine
chart this is the prime-spectrum zero locus. The inverse image of this zero locus
under Spec(B -> R) is the zero locus of K(U)R. Transporting the latter ideal along
GammaSpecIso shows that the complement of Q.support is g inverse of the complement
of K.support. Base change f over this open: associativity of pullbacks identifies its
projection with the base change of pullback.snd f (the inclusion of K's complement).
That morphism is an isomorphism by hypothesis, and its base change is an isomorphism.
This argument uses no flatness or properness, and includes empty complements and a
zero completion ring. -/
theorem completedAffine_complement_base_change
    {X Y : Scheme.{u}} (J K : Y.IdealSheafData) (f : X ⟶ Y)
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (U : Y.affineOpens) :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let L := (K.ideal U).map (algebraMap B R)
    let Q := Scheme.IdealSheafData.ofIdealTop
      (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    let g : Spec (CommRingCat.of R) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ U.2.isoSpec.inv ≫ U.1.ι
    IsIso (pullback.snd (pullback.snd f g) (Scheme.Opens.ι Q.support.compl)) := by
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let L := (K.ideal U).map (algebraMap B R)
  let S := Spec (CommRingCat.of R)
  let Q := Scheme.IdealSheafData.ofIdealTop
    (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
    U.2.isoSpec.inv ≫ U.1.ι
  have hk : U.2.fromSpec ⁻¹' (K.support : Set Y) =
      PrimeSpectrum.zeroLocus (K.ideal U : Set B) := by
    rw [← U.2.fromSpec_preimage_zeroLocus]
    ext x
    apply K.mem_support_iff_of_mem
    exact (congrArg (fun s : Set Y ↦ U.2.fromSpec x ∈ s)
      U.2.range_fromSpec).mp (Set.mem_range_self x)
  have hq : (Q.support : Set S) = PrimeSpectrum.zeroLocus (L : Set R) := by
    dsimp [Q]
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop]
    simpa only [Ideal.map, Scheme.zeroLocus_span] using
      Spec_zeroLocus_eq_zeroLocus (R := CommRingCat.of R) (L : Set R)
  have hW : Q.support.compl = g ⁻¹ᵁ K.support.compl := by
    apply TopologicalSpace.Opens.ext
    change (Q.support : Set S)ᶜ = (g ⁻¹' (K.support : Set Y))ᶜ
    congr 1
    rw [hq]
    change _ = (Spec.map (CommRingCat.ofHom (algebraMap B R))) ⁻¹'
      (U.2.fromSpec ⁻¹' (K.support : Set Y))
    rw [hk]
    change _ = (PrimeSpectrum.comap (algebraMap B R)) ⁻¹'
      PrimeSpectrum.zeroLocus (K.ideal U : Set B)
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    simp only [L, Ideal.map, PrimeSpectrum.zeroLocus_span]
    rfl
  let V : Y.Opens := K.support.compl
  let W := g ⁻¹ᵁ V
  let t := g ∣_ V
  have ht : t ≫ V.ι = W.ι ≫ g := morphismRestrict_ι g V
  let e := pullbackLeftPullbackSndIso f g W.ι
  let e' := pullbackLeftPullbackSndIso f V.ι t
  have : IsIso (pullback.snd f V.ι) := hV
  have hi : IsIso (pullback.snd f (t ≫ V.ι)) := by
    have he : e'.inv ≫ pullback.snd (pullback.snd f V.ι) t =
        pullback.snd f (t ≫ V.ι) := by simp [e']
    rw [← he]
    infer_instance
  have hi' : IsIso (pullback.snd f (W.ι ≫ g)) := by
    rw [← ht]
    exact hi
  have he : e.hom ≫ pullback.snd f (W.ι ≫ g) =
      pullback.snd (pullback.snd f g) W.ι := by simp [e]
  change IsIso (pullback.snd (pullback.snd f g) (Scheme.Opens.ι Q.support.compl))
  rw [hW, ← he]
  infer_instance

end AlgebraicGeometry
