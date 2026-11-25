/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

-- Restrict kernel sections to affine opens, multiply there, and use separatedness.
set_option backward.isDefEq.respectTransparency false in
private theorem square_zero_global_kernel {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [QuasiCompact f] (hf : f.ker * f.ker ≤ ⊥) :
    RingHom.ker f.appTop.hom * RingHom.ker f.appTop.hom ≤ ⊥ := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  apply Ideal.mem_bot.mpr
  apply Y.IsSheaf.section_ext
  intro y hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨U, le_top, hyU, ?_⟩
  have restrict_mem (c : Γ(Y, ⊤)) (hc : c ∈ RingHom.ker f.appTop.hom) :
      Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c ∈
        f.ker.ideal ⟨U, hU⟩ := by
    rw [Hom.ker_apply, RingHom.mem_ker]
    rw [← CommRingCat.comp_apply, f.naturality]
    simp only [CommRingCat.comp_apply]
    have hc0 := RingHom.mem_ker.mp hc
    simp only [Hom.appTop] at hc0
    change (Z.presheaf.map _).hom ((f.app ⊤).hom c) = 0
    exact (congrArg (Z.presheaf.map
      ((TopologicalSpace.Opens.map f.base).map (homOfLE (show U ≤ ⊤ from le_top))).op).hom
      hc0).trans (map_zero _)
  have hprod := hf ⟨U, hU⟩
    (Ideal.mul_mem_mul (restrict_mem a ha) (restrict_mem b hb))
  simpa only [IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot, map_mul, map_zero]
    using hprod

/-- The kernel ideal of the relative restriction map is square-zero.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-square-zero-relative-section-kernel-ideal)

Proof: On affine charts the kernel is the quotient ideal `I/J`; its product is
zero because `I * I ≤ J`. Pulling back to affine charts of an etale object
preserves this product inclusion, and the sheaf condition glues the resulting
ideal inclusion. -/
theorem relativeSectionKernel_ker_mul_le_bot (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J)
    (V : J.subscheme.Etaleᵒᵖ) :
    RingHom.ker ((etaleStructurePresheafToPullback
      (IdealSheafData.inclusion hJI)).app V).hom *
        RingHom.ker ((etaleStructurePresheafToPullback
          (IdealSheafData.inclusion hJI)).app V).hom ≤ ⊥ := by
  let i := IdealSheafData.inclusion hJI
  have hi : i.ker = I.comap J.subschemeι := by
    have hmap : i.ker.map J.subschemeι = I := by
      rw [IdealSheafData.map_ker, IdealSheafData.inclusion_subschemeι,
        IdealSheafData.ker_subschemeι]
    exact (IdealSheafData.comap_map_of_isClosedImmersion J.subschemeι i.ker).symm.trans
      (congrArg (fun K ↦ K.comap J.subschemeι) hmap)
  have hs : i.ker * i.ker ≤ ⊥ := by
    rw [hi, ← IdealSheafData.comap_mul]
    exact (IdealSheafData.comap_mono J.subschemeι hII).trans_eq
      (IdealSheafData.comap_subschemeι J)
  have hp : (pullback.fst V.unop.hom i).ker *
      (pullback.fst V.unop.hom i).ker ≤ ⊥ := by
    rw [IdealSheafData.ker_fst_of_isClosedImmersion,
      ← IdealSheafData.comap_mul]
    exact (IdealSheafData.comap_mono V.unop.hom hs).trans_eq
      (IdealSheafData.comap_bot V.unop.hom)
  exact square_zero_global_kernel (pullback.fst V.unop.hom i) hp

end AlgebraicGeometry.Scheme
