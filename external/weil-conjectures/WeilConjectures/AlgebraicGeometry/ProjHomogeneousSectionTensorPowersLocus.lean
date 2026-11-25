/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
@[expose] public section
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The nonvanishing locus of a homogeneous section is the corresponding standard open.
Source: Stacks Project, Constructions, Tags 01MS, 01MV and 01NG.
Proof: The coordinate opens D_+(x_i) cover polynomial Proj. On this chart O(d) has
basis x_i^d, and the section induced by f has coefficient f/x_i^d. Its value in the
one-dimensional residue-field fibre is nonzero if and only if that coefficient
is outside the corresponding prime of the degree-zero localization. By the
standard-open dictionary this means the homogeneous prime does not contain f,
exactly membership in D_+(f). The equality on all charts gives equality of sets.
For f=0 both sets are empty, including for positive d.
(blueprint: lem-sc-p1-homogeneous-section-tensor-powers-locus) -/
theorem proj_homogeneous_section_tensor_powers_locus (k : Type u) [Field k]
    {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    let L := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ))
    ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f :
        (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens) : Set _) =
        nonvanishingLocus L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) := by
  set_option backward.isDefEq.respectTransparency false in
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let L := Proj.twist 𝒜 (0 + (d : ℤ))
  let s := (Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)
  change (Proj.basicOpen 𝒜 f : Set _) = nonvanishingLocus L s
  have hcov : ∀ x : Proj 𝒜, ∃ g ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 g := by
    intro x
    have hx : x ∈ ⨆ i : Fin 2, Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
      rw [Proj.iSup_basicOpen_eq_top' 𝒜
        (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
        (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
        (MvPolynomial.adjoin_range_X_eq_top (Fin 2) k)]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨_, MvPolynomial.isHomogeneous_X k i, hi⟩
  have : L.IsInvertible := Proj.isInvertible_twist 𝒜 _ hcov
  ext x
  rw [mem_nonvanishingLocus_iff_generatesAt]
  obtain ⟨g, hg, hxg⟩ := hcov x
  have hgd : g ^ d ∈ 𝒜 d := by
    simpa [𝒜] using SetLike.pow_mem_graded d hg
  have hxgd : x ∈ Proj.basicOpen 𝒜 (g ^ d) := by
    rwa [Proj.basicOpen_pow 𝒜 g d hd]
  let U := Proj.basicOpen 𝒜 (g ^ d)
  let e := (Proj.unitToTwist hgd).app U (unitSectionsEquiv U 1)
  have he : IsFreeGenerator (M := L) e := Proj.isFreeGenerator_unitToTwist hgd
  let c := Proj.awayToSection 𝒜 (g ^ d)
    (HomogeneousLocalization.Away.mk 𝒜 hgd 1 f (by simpa only [one_smul] using hf))
  have hs : L.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s = c • e := by
    have h := Proj.map_unitToTwist_eq_smul hf hgd (by simpa only [one_smul] using hf)
    change L.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s =
      c • L.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
        ((Proj.unitToTwist hgd).app ⊤ (unitSectionsEquiv ⊤ 1)) at h
    have hres : L.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
        ((Proj.unitToTwist hgd).app ⊤ (unitSectionsEquiv ⊤ 1)) = e := by
      rw [← Hom.app_presheaf_map]
      erw [presheaf_map_unitSectionsEquiv]
      rw [map_one]
    rw [hres] at h
    exact h
  rw [generatesAt_iff_mem_basicOpen he hs hxgd,
    Proj.mem_basicOpen_iff_isUnit_val c hxgd]
  change x ∈ Proj.basicOpen 𝒜 f ↔ IsUnit (c.1 ⟨x, hxgd⟩).val
  dsimp only [c]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply,
    IsLocalization.AtPrime.isUnit_mk'_iff, Proj.mem_basicOpen]
  rfl
end AlgebraicGeometry
