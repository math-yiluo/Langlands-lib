/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Topology.ModuleMayerVietoris
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing

/-! # Local bounds uniform in the quasi-coherent coefficient module

Source: Stacks Project, Tag 01XJ, finite-cover argument over an affine base.
(blueprint: lem-pc-local-uniform-higher-direct-image-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isZero_openCohomology_union
    (Y : Scheme.{u}) (F : Y.Modules) (A B : Y.Opens) (q : ℕ)
    (hA : IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace (q + 1) A).obj F))
    (hB : IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace (q + 1) B).obj F))
    (hAB : IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace q (A ⊓ B)).obj F)) :
    IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace (q + 1) (A ⊔ B)).obj F) := by
  obtain ⟨δ, _, hexact, _⟩ := RingedSpace.module_mayerVietoris Y.toRingedSpace
  have hleft := AddCommGrpCat.subsingleton_of_isZero hA
  have hright := AddCommGrpCat.subsingleton_of_isZero hB
  have hsource := AddCommGrpCat.subsingleton_of_isZero hAB
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ ?_⟩
  have hx := (hexact A B F q).2.2 x
  obtain ⟨z, hz⟩ := hx.mp (by
    apply Prod.ext <;> exact Subsingleton.elim _ _)
  have hx0 : x = 0 := by
    rw [← hz, Subsingleton.elim z 0, map_zero]
  have hy := (hexact A B F q).2.2 y
  obtain ⟨z, hz⟩ := hy.mp (by
    apply Prod.ext <;> exact Subsingleton.elim _ _)
  have hy0 : y = 0 := by
    rw [← hz, Subsingleton.elim z 0, map_zero]
  exact hx0.trans hy0.symm

/-- Every point has a neighbourhood with a higher-direct-image bound independent of
its quasi-coherent coefficient module. The target need not be quasi-compact.
Source: Stacks Project, Tag 01XJ, proof of (3), affine-base finite-cover argument.
(blueprint: lem-pc-local-uniform-higher-direct-image-bound).

Proof: Choose an affine neighbourhood U of s and put Y=f^{-1}U, T=U and g=f|_U.
The scheme Y is quasi-compact and quasi-separated. Apply quasi-compact-open induction
to P(W): there exists n such that for every quasi-coherent F on Y and every affine
open V of T, H^p(W intersect g^{-1}V,F) vanishes for p >= n. For affine W take n=1:
the map W to T is affine, so W intersect g^{-1}V is affine, and affine-open module
cohomology vanishes. For W=A union B combine bounds a,b,c for A,B,A intersect B.
Mayer-Vietoris shows vanishing at p=q+1 when the two degree-p terms on A and B and
the degree-q intersection term vanish. Thus max(max(a,b),c)+1 is a bound.
At W=Y this gives a bound independent of F and V. Restrict M to Y; it stays
quasi-coherent. Apply the affine-basis higher-direct-image vanishing criterion,
which uses the sheafified cohomology presheaf and restriction of injective resolutions.
Only affine open base changes are needed for this local conclusion; arbitrary affine
base changes are unnecessary. The empty affine chart and empty Y are included. -/
theorem exists_local_uniform_higherDirectImage_bound
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (s : S) :
    ∃ (U : S.Opens) (n : ℕ), s ∈ U ∧
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)), M.IsQuasicoherent →
        ∀ p : ℕ, n ≤ p → IsZero
          (Scheme.Modules.restrict
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M)
            U.ι) := by
  obtain ⟨U, hU, hs, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  let Y := (f ⁻¹ᵁ U).toScheme
  let T := U.toScheme
  let g : Y ⟶ T := f ∣_ U
  have : IsAffine T := hU
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  let P : Y.Opens → Prop := fun W ↦ ∃ n : ℕ,
    ∀ (F : Y.Modules), F.IsQuasicoherent → ∀ (V : T.Opens), IsAffineOpen V →
      ∀ p : ℕ, n ≤ p →
        IsZero ((RingedSpace.openModuleCohomology Y.toRingedSpace p
          (W ⊓ g ⁻¹ᵁ V)).obj F)
  have hP : ∀ W : Y.Opens, IsCompact (W : Set Y) → P W := by
    apply quasiCompactOpen_induction Y P
    · intro W hW
      refine ⟨1, fun F hF V hV p hp ↦ ?_⟩
      have := hF
      have : IsAffine W.toScheme := hW
      have hpre := hV.preimage (W.ι ≫ g)
      have him := W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hpre
      have hWV : IsAffineOpen (W ⊓ g ⁻¹ᵁ V) := by
        simpa only [Scheme.Hom.comp_preimage,
          Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] using him
      have := subsingleton_openModuleCohomology_of_isAffineOpen Y F
        (W ⊓ g ⁻¹ᵁ V) hWV p (by omega)
      exact AddCommGrpCat.isZero_of_subsingleton _
    · intro A B _ _ hA hB hAB
      obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := hB
      obtain ⟨c, hc⟩ := hAB
      refine ⟨max (max a b) c + 1, fun F hF V hV p hp ↦ ?_⟩
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      have hqa : a ≤ q + 1 := by omega
      have hqb : b ≤ q + 1 := by omega
      have hqc : c ≤ q := by omega
      have h := isZero_openCohomology_union Y F (A ⊓ g ⁻¹ᵁ V)
        (B ⊓ g ⁻¹ᵁ V) q (ha F hF V hV (q + 1) hqa)
        (hb F hF V hV (q + 1) hqb)
        (by simpa only [inf_assoc, inf_left_comm, inf_idem] using hc F hF V hV q hqc)
      simpa only [inf_sup_right] using h
  obtain ⟨n, hn⟩ := hP ⊤ isCompact_univ
  refine ⟨U, n, hs, fun M hM p hp ↦ ?_⟩
  have := hM
  apply isZero_restrict_higherDirectImage_of_affine_basis f U M p
  intro V hV
  have hF : (Scheme.Modules.restrict M (f ⁻¹ᵁ U).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ U).ι M
  simpa only [top_inf_eq] using
    hn (Scheme.Modules.restrict M (f ⁻¹ᵁ U).ι) hF V hV p hp

end AlgebraicGeometry
