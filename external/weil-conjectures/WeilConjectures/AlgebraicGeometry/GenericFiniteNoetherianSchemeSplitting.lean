/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.GenericFiniteSchemeSplitting
import WeilConjectures.AlgebraicGeometry.FiniteSplittingClosedImmersionDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic splitting over a Noetherian scheme

Source: the proof of `lem-weil-pbc-finite-module-generic-reflection`, step 1,
using Stacks Project Tags 095K, 0959 and 04DZ.
(blueprint: lem-weil-pbc-generic-finite-noetherian-scheme-splitting)
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem splitting_partition_iso
    {P Q T : Scheme.{u}} (e : P ≅ Q) (p : P ⟶ T) (q : Q ⟶ T)
    (he : e.hom ≫ q = p) (n : ℕ) (W : Fin n → Q.Opens)
    (hcover : (⨆ j, W j) = ⊤)
    (hdisjoint : Pairwise (fun j k ↦ Disjoint (W j) (W k)))
    (hW : ∀ j, IsUniversalHomeomorphism ((W j).ι ≫ q)) :
    ∃ W' : Fin n → P.Opens,
      (⨆ j, W' j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W' j) (W' k)) ∧
      ∀ j, IsUniversalHomeomorphism ((W' j).ι ≫ p) := by
  let W' : Fin n → P.Opens := fun j ↦ e.hom ⁻¹ᵁ W j
  refine ⟨W', ?_, ?_, ?_⟩
  · simp only [W', ← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  · intro j k hjk
    apply disjoint_iff.mpr
    rw [← Scheme.Hom.preimage_inf, disjoint_iff.mp (hdisjoint hjk)]
    exact Scheme.Hom.preimage_bot _
  · intro j
    have : IsUniversalHomeomorphism ((W j).ι ≫ q) := hW j
    have hfac : (W' j).ι ≫ p = (e.hom ∣_ W j) ≫ ((W j).ι ≫ q) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, he]
    rw [hfac]
    infer_instance

private theorem reduced_generic_finite_splitting
    {X Y : Scheme.{u}} [IsNoetherian Y] [IsReduced Y] (f : X ⟶ Y) [IsFinite f]
    (V : Y.Opens) (hV : Dense (V : Set Y)) :
    ∃ U : Y.Opens, U ≤ V ∧ Dense (U : Set Y) ∧
      ∃ 𝒯 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
        ∃ (n : ℕ) (W : Fin n → (pullback (𝒯.f i) (f ∣_ U)).Opens),
          (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
          ∀ j, IsUniversalHomeomorphism
            ((W j).ι ≫ pullback.fst (𝒯.f i) (f ∣_ U)) := by
  classical
  let I := {A : Y.affineOpens // A.1 ≤ V ∧ IsIntegral A.1.toScheme}
  have hlocal (a : I) :
      ∃ D : a.1.1.toScheme.Opens, Dense (D : Set a.1.1.toScheme) ∧
        ∃ (T : Scheme.{u}) (p : T ⟶ D.toScheme),
          IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ (n : ℕ) (W : Fin n → (pullback (f ∣_ a.1.1) (p ≫ D.ι)).Opens),
            (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
            ∀ j, IsUniversalHomeomorphism
              ((W j).ι ≫ pullback.snd (f ∣_ a.1.1) (p ≫ D.ι)) := by
    have : IsIntegral a.1.1.toScheme := a.2.2
    have : IsAffine a.1.1.toScheme := a.1.2
    have : IsNoetherian a.1.1.toScheme := isNoetherian_of_locallyOfFiniteType a.1.1.ι
    obtain ⟨D, hD, hs⟩ := exists_dense_open_finite_scheme_splitting _ (f ∣_ a.1.1)
    exact ⟨D, hD, hs D le_rfl⟩
  choose D hD T p hpfin hpeta hpsurj n W hcover hdisjoint hW using hlocal
  let B (a : I) : Y.Opens := a.1.1.ι ''ᵁ D a
  let U : Y.Opens := ⨆ a, B a
  have hBU (a : I) : B a ≤ U := le_iSup B a
  have hUV : U ≤ V := by
    apply iSup_le
    intro a
    exact (a.1.1.ι_image_le (D a)).trans a.2.1
  have hUdense : Dense (U : Set Y) := by
    intro x
    let C := irreducibleComponent x
    have hC : C ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents x
    let O : Y.Opens :=
      ⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, by
        rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
        exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
          (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)⟩
    have hOcl : closure (O : Set Y) = C :=
      closure_sUnion_irreducibleComponents_sdiff_singleton
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents C hC
    have hOsub : (O : Set Y) ⊆ C := by rw [← hOcl]; exact subset_closure
    have hOne : (O : Set Y).Nonempty := by
      by_contra! hempty
      exact hC.1.nonempty.ne_empty (by rw [← hOcl, hempty, closure_empty])
    obtain ⟨y, hy⟩ := hV.inter_open_nonempty (O : Set Y) O.isOpen hOne
    obtain ⟨_, ⟨A : Y.Opens, hA, rfl⟩, hyA, hAVO⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ V ⊓ O from ⟨hy.2, hy.1⟩) (V ⊓ O).isOpen
    have hAC : (A : Set Y) ⊆ C := fun z hz ↦ hOsub (hAVO hz).2
    have hAirr : IsIrreducible (A : Set Y) :=
      hC.1.2.subset_irreducible ⟨y, hyA⟩ A.isOpen subset_rfl hAC
    have : IrreducibleSpace A.toScheme := Subtype.irreducibleSpace hAirr
    have : IsIntegral A.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    let a : I := ⟨⟨A, hA⟩, (fun z hz ↦ (hAVO hz).1), inferInstance⟩
    have hAB : (A : Set Y) ⊆ closure (B a : Set Y) := by
      intro z hz
      exact image_closure_subset_closure_image A.ι.continuous
        ⟨⟨z, hz⟩, hD a _, rfl⟩
    have hCcl : C ⊆ closure (A : Set Y) := by
      have h := subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 A.isOpen
        (by simpa only [Set.inter_eq_right.mpr hAC] using (show (A : Set Y).Nonempty from
          ⟨y, hyA⟩))
      simpa only [Set.inter_eq_right.mpr hAC] using h
    exact closure_mono (hBU a)
      ((closure_minimal hAB isClosed_closure) (hCcl mem_irreducibleComponent))
  let t (a : I) : T a ⟶ U.toScheme :=
    p a ≫ (a.1.1.ι.isoImage (D a)).hom ≫ Y.homOfLE (hBU a)
  have ht (a : I) : t a ≫ U.ι = (p a ≫ (D a).ι) ≫ a.1.1.ι := by
    simp [t, B]
  have htcov (x : U.toScheme) : ∃ a y, t a y = x := by
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    obtain ⟨z, hz, hzx⟩ := ha
    obtain ⟨y, hy⟩ := (hpsurj a).1 ⟨z, hz⟩
    refine ⟨a, y, ?_⟩
    apply Subtype.ext
    change U.ι (t a y) = x.1
    rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    exact hzx
  have htet (a : I) : Etale (t a) := by
    have : Etale (p a) := hpeta a
    dsimp [t]
    infer_instance
  let 𝒯 : Cover.{u} etalePrecoverage U.toScheme := Cover.mkOfCovers I T t htcov htet
  refine ⟨U, hUV, hUdense, 𝒯, ?_⟩
  intro a
  have hP := (IsPullback.of_hasPullback (t a) (f ∣_ U)).paste_vert
    (isPullback_morphismRestrict f U)
  rw [ht] at hP
  have hQ := (IsPullback.of_hasPullback (f ∣_ a.1.1) (p a ≫ (D a).ι)).flip.paste_vert
    (isPullback_morphismRestrict f a.1.1)
  let e := hP.isoIsPullback _ _ hQ
  refine ⟨n a, ?_⟩
  exact splitting_partition_iso e _ _ (hP.isoIsPullback_hom_fst _ _ hQ)
    (n a) (W a) (hcover a) (hdisjoint a) (hW a)

/-- A finite morphism splits into universal homeomorphisms on an etale cover of a
smaller dense open. This assertion concerns schemes alone and has no sheaf hypothesis.

Source: `lem-weil-pbc-finite-module-generic-reflection`, proof step 1;
Stacks Project Tags 095K, 0959 and 04DZ.
(blueprint: lem-weil-pbc-generic-finite-noetherian-scheme-splitting)

Proof: Reduce the Noetherian target. Its finitely many irreducible components have
pairwise disjoint dense affine integral opens, after removing their intersections.
Intersect these opens with V. Apply `exists_dense_open_finite_scheme_splitting` to
its finite source over each such affine, and intersect with the dense splitting open.
The union of the resulting opens contains each generic point and is dense in the
reduced target, hence in the original target; it is contained in V. On each component
use the etale surjective cover supplied by the affine theorem. Etale schemes lift
uniquely across the nilpotent reduction immersion (04DZ); the lifted cover remains
surjective since reduction does not change points. The disjoint clopen components of
the reduced source lift uniquely to those of the original source. Each component map
is still a universal homeomorphism: both vertical reduction maps are universal
homeomorphisms, and universal injectivity, surjectivity and integrality are unchanged
by these nilpotent thickenings. Compose the lifted etale covers with their component
open immersions to obtain a cover of U. Pullbacks of the restricted morphism have the
asserted finite disjoint partitions. For the empty target take U empty and an empty
cover. Empty inverse images have the empty partition, whose union is top. -/
theorem exists_dense_open_finite_noetherian_scheme_splitting
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (V : Y.Opens) (hV : Dense (V : Set Y)) :
    ∃ U : Y.Opens, U ≤ V ∧ Dense (U : Set Y) ∧
      ∃ 𝒯 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
        ∃ (n : ℕ) (W : Fin n → (pullback (𝒯.f i) (f ∣_ U)).Opens),
          (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
          ∀ j, IsUniversalHomeomorphism
            ((W j).ι ≫ pullback.fst (𝒯.f i) (f ∣_ U)) := by
  let r := Y.nilradical.subschemeι
  have : Surjective r := ⟨by
    apply Set.range_eq_univ.mp
    change Set.range Y.nilradical.subschemeι = Set.univ
    simp [IdealSheafData.range_subschemeι]⟩
  have : IsNoetherian Y.nilradical.subscheme :=
    isNoetherian_of_locallyOfFiniteType r
  have hr := r.isHomeomorph
  obtain ⟨U₀, hU₀V, hU₀dense, hsplit⟩ :=
    reduced_generic_finite_splitting (pullback.snd f r) (r ⁻¹ᵁ V)
      (hV.preimage hr.isOpenMap)
  let U : Y.Opens := ⟨r '' (U₀ : Set Y.nilradical.subscheme),
    hr.isOpenMap _ U₀.isOpen⟩
  have hpre : r ⁻¹ᵁ U = U₀ := by
    apply TopologicalSpace.Opens.ext
    exact Set.preimage_image_eq _ hr.injective
  refine ⟨U, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hU₀V hy
  · exact hr.surjective.denseRange.dense_image r.continuous hU₀dense
  · apply finite_splitting_descends_surjective_closedImmersion f r U
    rw [hpre]
    exact hsplit

end AlgebraicGeometry.Scheme
