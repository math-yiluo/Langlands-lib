/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmpleIdealSection
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Ideal-supported affine sections of ample pullbacks

Source: Stacks Project, Properties, Proposition 01Q3 and Lemma 01PV.
(blueprint: lem-sc-ample-pullback-ideal-affine-section).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem nonvanishing_tensor {X : Scheme.{u}} (M N : X.Modules)
    [M.IsInvertible] [N.IsInvertible] (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    nonvanishingLocus (M ⊗ N) (tmulSection s t) =
      nonvanishingLocus M s ∩ nonvanishingLocus N t := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  ext x
  obtain ⟨U, hxU, _, ⟨e, he⟩, d, hd⟩ := exists_isFreeGenerator₂ M N
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨a, ha⟩ := he.exists_smul_eq (M.presheaf.map (homOfLE le_top).op s)
  obtain ⟨b, hb⟩ := hd.exists_smul_eq (N.presheaf.map (homOfLE le_top).op t)
  have hp : (M ⊗ N).presheaf.map (homOfLE le_top).op (tmulSection s t) =
      (a * b) • tmulSection e d := by
    rw [tmulSection_map, ← ha, ← hb, smul_tmulSection, tmulSection_smul, smul_smul]
  change x ∈ nonvanishingLocus (M ⊗ N) _ ↔
    x ∈ nonvanishingLocus M s ∧ x ∈ nonvanishingLocus N t
  rw [mem_nonvanishingLocus_iff_generatesAt,
    mem_nonvanishingLocus_iff_generatesAt, mem_nonvanishingLocus_iff_generatesAt,
    generatesAt_iff_mem_basicOpen (he.tmulSection hd) hp hxU,
    generatesAt_iff_mem_basicOpen he ha.symm hxU,
    generatesAt_iff_mem_basicOpen hd hb.symm hxU, X.basicOpen_mul]
  rfl

private theorem ideal_image_disjoint {X : Scheme.{u}} (J : X.IdealSheafData)
    (N : X.Modules) [N.IsInvertible] (v : Γ(J.toModules ⊗ N, ⊤)) :
    Disjoint (nonvanishingLocus N
      ((J.toModulesι ▷ N ≫ (λ_ N).hom).app ⊤ v)) (J.support : Set X) := by
  have := IsInvertible.sheafOfModules_isInvertible N
  rw [Set.disjoint_left]
  intro x hx hJ
  obtain ⟨U, hxU, _, e, he⟩ := exists_isFreeGenerator N
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨a, ha⟩ := (he.bijective_tmulSection_right (M := J.toModules) le_rfl).2
    ((J.toModules ⊗ N).presheaf.map (homOfLE le_top).op v)
  simp only [presheaf_map_id_apply] at ha
  let c : Γ(X, U.1) := J.toModulesι.app U.1 a
  have hc : c ∈ J.ideal U := (J.range_toModulesι_app U).subset ⟨a, rfl⟩
  have himg : N.presheaf.map (homOfLE le_top).op
      ((J.toModulesι ▷ N ≫ (λ_ N).hom).app ⊤ v) = c • e := by
    rw [← Hom.app_presheaf_map, ← ha, Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerRight_app_tmulSection]
    exact leftUnitor_hom_app_tmulSection' _ _
  have hxc := mem_basicOpen_of_generatesAt he himg hxU
    ((mem_nonvanishingLocus_iff_generatesAt _ _ _).mp hx)
  have hz := (J.mem_support_iff_of_mem hxU).mp hJ
  rw [X.mem_zeroLocus_iff] at hz
  exact hz c hc hxc

private theorem ideal_image_map {X : Scheme.{u}} (J : X.IdealSheafData)
    {M N : X.Modules} (a : M ⟶ N) (v : Γ(J.toModules ⊗ M, ⊤)) :
    (J.toModulesι ▷ N ≫ (λ_ N).hom).app ⊤ ((J.toModules ◁ a).app ⊤ v) =
      a.app ⊤ ((J.toModulesι ▷ M ≫ (λ_ M).hom).app ⊤ v) := by
  have h : J.toModules ◁ a ≫ J.toModulesι ▷ N ≫ (λ_ N).hom =
      (J.toModulesι ▷ M ≫ (λ_ M).hom) ≫ a := by
    let i : J.toModules ⟶ 𝟙_ X.Modules := J.toModulesι
    change J.toModules ◁ a ≫ i ▷ N ≫ (λ_ N).hom = (i ▷ M ≫ (λ_ M).hom) ≫ a
    rw [whisker_exchange_assoc, leftUnitor_naturality]
    simp only [Category.assoc]
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply] using
    congrArg (fun b ↦ b.app ⊤ v) h

private theorem ideal_image_tensor {X : Scheme.{u}} (J : X.IdealSheafData)
    (M N : X.Modules) (v : Γ(J.toModules ⊗ M, ⊤)) (t : Γ(N, ⊤)) :
    (J.toModulesι ▷ (M ⊗ N) ≫ (λ_ (M ⊗ N)).hom).app ⊤
        ((α_ J.toModules M N).hom.app ⊤ (tmulSection v t)) =
      tmulSection ((J.toModulesι ▷ M ≫ (λ_ M).hom).app ⊤ v) t := by
  have h : (α_ J.toModules M N).hom ≫ J.toModulesι ▷ (M ⊗ N) ≫
      (λ_ (M ⊗ N)).hom = (J.toModulesι ▷ M ≫ (λ_ M).hom) ▷ N := by
    let i : J.toModules ⟶ 𝟙_ X.Modules := J.toModulesι
    change (α_ J.toModules M N).hom ≫ i ▷ (M ⊗ N) ≫ (λ_ (M ⊗ N)).hom =
      (i ▷ M ≫ (λ_ M).hom) ▷ N
    rw [← associator_naturality_left_assoc, leftUnitor_tensor_hom]
    simp only [Iso.hom_inv_id_assoc, comp_whiskerRight]
  have hh := congrArg (fun b ↦ b.app ⊤ (tmulSection v t)) h
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply,
    whiskerRight_app_tmulSection] using hh

private theorem pullback_ideal_section {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) [L.IsInvertible] [((tensorPullback f).obj L).IsInvertible]
    (J : Y.IdealSheafData) (n : ℕ)
    (v : Γ(J.toModules ⊗ ((tensorPullback f).obj L).tensorPow n, ⊤)) :
    ∃ v' : Γ(J.toModules ⊗ (tensorPullback f).obj (L.tensorPow n), ⊤),
      nonvanishingLocus ((tensorPullback f).obj (L.tensorPow n))
          ((J.toModulesι ▷ (tensorPullback f).obj (L.tensorPow n) ≫
            (λ_ ((tensorPullback f).obj (L.tensorPow n))).hom).app ⊤ v') =
      nonvanishingLocus (((tensorPullback f).obj L).tensorPow n)
          ((J.toModulesι ▷ ((tensorPullback f).obj L).tensorPow n ≫
            (λ_ (((tensorPullback f).obj L).tensorPow n)).hom).app ⊤ v) := by
  classical
  let a := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  obtain ⟨b⟩ := nonempty_pullback_tensorPow_iso f L n
  obtain ⟨c⟩ := tensorPow_iso (a.app L).symm n
  let e := (a.app (L.tensorPow n) ≪≫ b ≪≫ c).symm
  have : ((tensorPullback f).obj (L.tensorPow n)).IsInvertible :=
    IsInvertible.of_iso e
  refine ⟨(J.toModules ◁ e.hom).app ⊤ v, ?_⟩
  rw [ideal_image_map, nonvanishingLocus_iso e]

/-- An ample pullback admits ideal-supported affine power sections outside the ideal support.

Source: Stacks Project, Properties, Proposition 01Q3 and Lemma 01PV;
Varieties, Lemma 09NX, final paragraph.
(blueprint: lem-sc-ample-pullback-ideal-affine-section).

Proof: write M = f^* L. The ample ideal section theorem supplies a section of
J tensor M^p, with p positive, whose image is nonvanishing at y. Ampleness supplies
a section of M^q, q positive, with affine nonvanishing locus through y. Tensor these
sections and use the associator and the tensor-power addition isomorphism to obtain
a section of J tensor M^(p+q). Its image has locus the intersection of the two
original loci, since the modules are invertible and their fibres have rank one.
The affine-cap-section-open theorem makes this intersection affine. The ideal
inclusion has zero fibre at every point of its support, so the intersection avoids
that support. The canonical monoidal pullback isomorphism identifies M^(p+q) with
f^*(L^(p+q)); transport both the ideal-supported section and its image through this
isomorphism. Naturality of the left unitor identifies the transported image with
the ideal inclusion tensored with the identity followed by the left unitor.
An isomorphism preserves the maximal-ideal submodules of stalks, hence preserves
the nonvanishing locus. The exponent p+q is positive. -/
theorem exists_ample_pullback_ideal_affine_section
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [L.IsInvertible]
    [((tensorPullback f).obj L).IsInvertible]
    (hL : IsAmple Y ((tensorPullback f).obj L)) (J : Y.IdealSheafData)
    (y : Y) (hy : y ∉ (J.support : Set Y)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ v : Γ(J.toModules ⊗ (tensorPullback f).obj (L.tensorPow n), ⊤),
        ∃ V : Y.Opens, y ∈ V ∧ IsAffineOpen V ∧
          (V : Set Y) = nonvanishingLocus ((tensorPullback f).obj (L.tensorPow n))
            ((J.toModulesι ▷ (tensorPullback f).obj (L.tensorPow n) ≫
              (λ_ ((tensorPullback f).obj (L.tensorPow n))).hom).app ⊤ v) ∧
          Disjoint (V : Set Y) (J.support : Set Y) := by
  let M := (tensorPullback f).obj L
  let : CompactSpace Y := hL.1
  obtain ⟨p, hp, u, v, huv, hyu⟩ := Scheme.IdealSheafData.exists_section_of_ample_ideal M hL J hy
  obtain ⟨q, hq, t, U, hyU, hU, hUt⟩ := hL.2 y
  obtain ⟨V, hV, hVloc⟩ := (affine_cap_section_open Y (M.tensorPow p) u U hU).1
  let e := (M.tensorPowAddIso p q).symm
  let w : Γ(J.toModules ⊗ M.tensorPow (p + q), ⊤) :=
    (J.toModules ◁ e.hom).app ⊤
      ((α_ J.toModules (M.tensorPow p) (M.tensorPow q)).hom.app ⊤ (tmulSection v t))
  have hw : (J.toModulesι ▷ M.tensorPow (p + q) ≫
      (λ_ (M.tensorPow (p + q))).hom).app ⊤ w =
      e.hom.app ⊤ (tmulSection u t) := by
    dsimp only [w]
    rw [ideal_image_map, ideal_image_tensor]
    congr 2
    simpa only [tensorHom_id] using huv.symm
  have hloc : nonvanishingLocus (M.tensorPow (p + q))
      ((J.toModulesι ▷ M.tensorPow (p + q) ≫
        (λ_ (M.tensorPow (p + q))).hom).app ⊤ w) =
      nonvanishingLocus (M.tensorPow p) u ∩ nonvanishingLocus (M.tensorPow q) t := by
    rw [hw, nonvanishingLocus_iso e, nonvanishing_tensor]
  have hVeq : (V : Set Y) = nonvanishingLocus (M.tensorPow (p + q))
      ((J.toModulesι ▷ M.tensorPow (p + q) ≫
        (λ_ (M.tensorPow (p + q))).hom).app ⊤ w) := by
    rw [hloc]
    ext x
    exact (hVloc x).trans ((and_comm).trans (and_congr_right (fun _ ↦ hUt x)))
  have hyV : y ∈ V := (hVloc y).mpr ⟨hyU, hyu⟩
  have hdisj : Disjoint (V : Set Y) (J.support : Set Y) := by
    rw [hVeq]
    exact ideal_image_disjoint J (M.tensorPow (p + q)) w
  obtain ⟨w', hw'⟩ := pullback_ideal_section f L J (p + q) w
  exact ⟨p + q, Nat.add_pos_left hp q, w', V, hyV, hV, hw' ▸ hVeq, hdisj⟩

end AlgebraicGeometry.Scheme.Modules
