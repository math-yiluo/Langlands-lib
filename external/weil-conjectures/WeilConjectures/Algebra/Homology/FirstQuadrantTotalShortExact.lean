/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-! # Exactness of finite-diagonal totalization

Source: Stacks Project, tag 012X, the finite-diagonal total complex construction.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
  L.HasTotal (ComplexShape.up ℕ)]

/-- Totalize a short complex of first-quadrant bicomplexes and extend by zero. -/
noncomputable def totalExtendShortComplex
    (S : ShortComplex (HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.extendMap (total.map S.f (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (total.map S.g (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, ← total.map_comp, S.zero,
        total.map_zero, HomologicalComplex.extendMap_zero])

local instance : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts

private noncomputable def diagonalShortComplex {J : Type} [Finite J]
    (S : J → ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (biproduct.map (fun j ↦ (S j).f))
    (biproduct.map (fun j ↦ (S j).g)) (by
      ext j
      simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
      rw [← Category.assoc, (S j).zero]
      simp)

omit [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
  L.HasTotal (ComplexShape.up ℕ)] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma diagonalShortComplex_shortExact {J : Type} [Finite J]
    (S : J → ShortComplex C) (hS : ∀ j, (S j).ShortExact) :
    (diagonalShortComplex S).ShortExact := by
  unfold diagonalShortComplex
  have hm (j : J) : Mono (S j).f := (hS j).mono_f
  have he (j : J) : Epi (S j).g := (hS j).epi_g
  refine ShortComplex.ShortExact.mk' ?_
    (inferInstanceAs (Mono (biproduct.map (fun j ↦ (S j).f))))
    (inferInstanceAs (Epi (biproduct.map (fun j ↦ (S j).g))))
  apply ShortComplex.exact_of_f_is_kernel
  refine Fork.IsLimit.mk _ (fun s ↦ biproduct.lift (fun j ↦
    (hS j).exact.fIsKernel.lift (KernelFork.ofι
      (s.ι ≫ biproduct.π (fun j ↦ (S j).X₂) j) ?_))) ?_ ?_
  · rw [Category.assoc, ← biproduct.map_π (fun j ↦ (S j).g) j,
      ← Category.assoc, KernelFork.condition, zero_comp]
  · intro s
    change biproduct.lift _ ≫ biproduct.map (fun j ↦ (S j).f) = s.ι
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.map_π, ← Category.assoc, biproduct.lift_π]
    exact Fork.IsLimit.lift_ι (hS j).exact.fIsKernel
  · intro s m hm
    apply biproduct.hom_ext
    intro j
    apply (cancel_mono (S j).f).1
    rw [Category.assoc, biproduct.lift_π]
    erw [Fork.IsLimit.lift_ι]
    change m ≫ biproduct.π (fun j ↦ (S j).X₁) j ≫ (S j).f =
      s.ι ≫ biproduct.π (fun j ↦ (S j).X₂) j
    rw [← biproduct.map_π (fun j ↦ (S j).f) j, ← Category.assoc]
    change m ≫ biproduct.map (fun j ↦ (S j).f) = s.ι at hm
    rw [hm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Finite-diagonal totalization, followed by extension by zero, preserves short exactness.
Source: Stacks Project, tag 012X, definition of the total complex and finite diagonals.
(blueprint: lem-sp-first-quadrant-total-extend-short-exact).

Proof: evaluate the short complex in bidegree (p,q). Evaluation in either complex
category preserves kernels and cokernels, so the resulting sequence in C is short exact.
In total degree n take the finite direct sum of these sequences over p+q=n. In an
abelian category finite biproducts preserve kernels and cokernels, hence this sum is
short exact. These sums are exactly the components of the two totalized maps.
The degreewise criterion for short exactness proves the claim over the naturals.
Extension by zero has the same sequences in nonnegative degrees and a zero sequence
in each negative degree, so the criterion applies again over the integers. -/
theorem totalExtendShortComplex_shortExact
    (S : ShortComplex (HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (hS : S.ShortExact) : (totalExtendShortComplex S).ShortExact := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  let T : ShortComplex (CochainComplex C ℕ) :=
    ShortComplex.mk (total.map S.f (ComplexShape.up ℕ))
      (total.map S.g (ComplexShape.up ℕ))
      (by rw [← total.map_comp, S.zero, total.map_zero])
  have hT : T.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let J := {i : ℕ × ℕ // i.1 + i.2 = n}
    have : Finite J := by
      apply Set.Finite.to_subtype
      exact (Set.finite_Iic (n, n)).subset (by
        rintro ⟨p, q⟩ (h : p + q = n)
        simp only [Set.mem_Iic, Prod.mk_le_mk]
        omega)
    let R (j : J) : ShortComplex C :=
      (S.map (HomologicalComplex.eval _ _ j.val.1)).map
        (HomologicalComplex.eval _ _ j.val.2)
    have hR (j : J) : (R j).ShortExact := by
      have hs := hS.map (HomologicalComplex.eval _ _ j.val.1)
      have := hs.mono_f
      have := hs.epi_g
      exact hs.map (HomologicalComplex.eval _ _ j.val.2)
    apply ShortComplex.shortExact_of_iso _ (diagonalShortComplex_shortExact R hR)
    refine ShortComplex.isoMk
      (biproduct.isoCoproduct (fun j : J ↦ (R j).X₁))
      (biproduct.isoCoproduct (fun j : J ↦ (R j).X₂))
      (biproduct.isoCoproduct (fun j : J ↦ (R j).X₃)) ?_ ?_
    all_goals
      dsimp [diagonalShortComplex, T, R]
      apply biproduct.hom_ext'
      intro j
      simp only [biproduct.ι_map_assoc, biproduct.isoCoproduct_hom,
        biproduct.ι_desc_assoc, biproduct.ι_desc]
      first
      | exact ιTotal_map S.X₁ S.X₂ S.f (ComplexShape.up ℕ) j.val.1 j.val.2 n j.property
      | exact ιTotal_map S.X₂ S.X₃ S.g (ComplexShape.up ℕ) j.val.1 j.val.2 n j.property
  have := hT.mono_f
  have := hT.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    apply ShortComplex.shortExact_of_iso _
      (hT.map (HomologicalComplex.eval _ _ n))
    refine ShortComplex.isoMk
      ((T.X₁).extendXIso ComplexShape.embeddingUpNat hn).symm
      ((T.X₂).extendXIso ComplexShape.embeddingUpNat hn).symm
      ((T.X₃).extendXIso ComplexShape.embeddingUpNat hn).symm ?_ ?_
    all_goals
      dsimp [totalExtendShortComplex, T]
      rw [HomologicalComplex.extendMap_f _ _ hn]
      simp
  · have hz (L : CochainComplex C ℕ) :
        IsZero ((L.extend ComplexShape.embeddingUpNat).X i) :=
      L.isZero_extend_X _ i (by simpa using hi)
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact ShortComplex.exact_of_isZero_X₂ _ (hz T.X₂)
    · exact (hz T.X₁).mono _
    · exact (hz T.X₃).epi _

end HomologicalComplex₂
