/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Algebra.Homology.ModuleCat.Subcomplex
public import WeilConjectures.Mathlib.Algebra.DirectSum.Module

/-!
# Telescopes and stupid truncations of complexes of modules

Let `L` be a cochain complex of `R`-modules.

* If `N 0 ≤ N 1 ≤ ⋯` is an increasing sequence of subcomplexes of `L` which exhausts `L`, then
  `0 ⟶ ∐ₙ N n ⟶ ∐ₙ N n ⟶ L ⟶ 0` is a short exact sequence of complexes, the first map being
  `𝟙 - shift` (`CochainComplex.telescopeShortComplex_shortExact`). In each degree this is the
  exact sequence `DirectSum.injective_id_sub_telescopeShift` etc.
* The stupid truncations `σ^{≥ a} L` (`CochainComplex.stupidTruncGEFamily`) are subcomplexes,
  and `0 ⟶ σ^{≥ a + 1} L ⟶ σ^{≥ a} L ⟶ Lᵃ[-a] ⟶ 0` is a short exact sequence of complexes
  (`CochainComplex.stupidTruncShortComplex_shortExact`).
* The bounded subcomplexes `σ^{≥ -m} τ^{≤ m} L` (`CochainComplex.truncFamily`) form an
  increasing sequence exhausting `L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CochainComplex

variable {R : Type u} [CommRing R] {L : CochainComplex (ModuleCat.{u} R) ℤ}

section Telescope

variable (N : ℕ → L.SubcomplexFamily) (hN : ∀ n, N n ≤ N (n + 1))

/-- The shift endomorphism of the coproduct of an increasing sequence of subcomplexes, mapping
the summand `N n` to the summand `N (n + 1)` by the inclusion. -/
noncomputable def telescopeShift :
    ∐ (fun n ↦ subcomplex (N n)) ⟶ ∐ (fun n ↦ subcomplex (N n)) :=
  Sigma.desc fun n ↦ subcomplexMap (hN n) ≫ Sigma.ι (fun n ↦ subcomplex (N n)) (n + 1)

/-- The short complex `∐ₙ N n ⟶ ∐ₙ N n ⟶ L` attached to an increasing sequence of
subcomplexes, the first map being `𝟙 - shift`. -/
@[simps]
noncomputable def telescopeShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) where
  X₁ := ∐ (fun n ↦ subcomplex (N n))
  X₂ := ∐ (fun n ↦ subcomplex (N n))
  X₃ := L
  f := 𝟙 _ - telescopeShift N hN
  g := Sigma.desc fun n ↦ subcomplexι (N n)
  zero := by
    ext n : 1
    simp [telescopeShift]

lemma monotone_subcomplexFamily_N {N : ℕ → L.SubcomplexFamily} (hN : ∀ n, N n ≤ N (n + 1))
    (i : ℤ) : Monotone fun n ↦ (N n).N i :=
  monotone_nat_of_le_succ fun n ↦ hN n i

/-- In degree `i`, the coproduct of the subcomplexes `N n` is the direct sum of the modules
`(N n).N i`. -/
noncomputable def sigmaSubcomplexXIso (i : ℤ) :
    (∐ (fun n ↦ subcomplex (N n))).X i ≅ ModuleCat.of R (DirectSum ℕ fun n ↦ (N n).N i) :=
  (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval _ _ i) _ _
    (coproductIsCoproduct fun n ↦ subcomplex (N n))).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit fun n ↦ (subcomplex (N n)).X i)

@[reassoc (attr := simp)]
lemma ι_sigmaSubcomplexXIso_hom (n : ℕ) (i : ℤ) :
    (Sigma.ι (fun n ↦ subcomplex (N n)) n).f i ≫ (sigmaSubcomplexXIso N i).hom =
      ModuleCat.ofHom (DirectSum.lof R ℕ (fun n ↦ (N n).N i) n) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval _ _ i) _ _
      (coproductIsCoproduct fun n ↦ subcomplex (N n)))
    (ModuleCat.coproductCoconeIsColimit fun n ↦ (subcomplex (N n)).X i) (Discrete.mk n)

/-- The jointly epimorphic family of the injections in a fixed degree. -/
lemma sigmaSubcomplex_hom_ext {i : ℤ} {Y : ModuleCat.{u} R}
    {f g : (∐ (fun n ↦ subcomplex (N n))).X i ⟶ Y}
    (h : ∀ n, (Sigma.ι (fun n ↦ subcomplex (N n)) n).f i ≫ f =
      (Sigma.ι (fun n ↦ subcomplex (N n)) n).f i ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval _ _ i) _ _
    (coproductIsCoproduct fun n ↦ subcomplex (N n))) _ _ h

/-- The degreewise exact sequence `0 ⟶ ⨁ₙ (N n)ⁱ ⟶ ⨁ₙ (N n)ⁱ ⟶ Lⁱ`. -/
noncomputable def telescopeShortComplexX (i : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk
    (LinearMap.id - DirectSum.telescopeShift _ (monotone_subcomplexFamily_N hN i))
    (DirectSum.telescopeSum fun n ↦ (N n).N i)
    (DirectSum.telescopeSum_comp_id_sub_telescopeShift _)

lemma id_sub_telescopeShift_f_comp (i : ℤ) :
    (𝟙 _ - telescopeShift N hN).f i ≫ (sigmaSubcomplexXIso N i).hom =
      (sigmaSubcomplexXIso N i).hom ≫ ModuleCat.ofHom (LinearMap.id -
        DirectSum.telescopeShift _ (monotone_subcomplexFamily_N hN i)) := by
  refine sigmaSubcomplex_hom_ext N fun n ↦ ?_
  rw [← HomologicalComplex.comp_f_assoc, ι_sigmaSubcomplexXIso_hom_assoc,
    Preadditive.comp_sub, Category.comp_id, telescopeShift, Sigma.ι_comp_desc,
    HomologicalComplex.sub_f_apply, Preadditive.sub_comp, HomologicalComplex.comp_f,
    Category.assoc, ι_sigmaSubcomplexXIso_hom, ι_sigmaSubcomplexXIso_hom]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_sub, ConcreteCategory.hom_ofHom, ModuleCat.hom_comp,
    LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    sub_right_inj]
  exact (DirectSum.telescopeShift_lof (N := fun n ↦ (N n).N i) _ n x).symm

lemma sigmaDesc_subcomplexι_f (i : ℤ) :
    (Sigma.desc fun n ↦ subcomplexι (N n)).f i = (sigmaSubcomplexXIso N i).hom ≫
      ModuleCat.ofHom (DirectSum.telescopeSum fun n ↦ (N n).N i) := by
  refine sigmaSubcomplex_hom_ext N fun n ↦ ?_
  rw [← HomologicalComplex.comp_f, Sigma.ι_comp_desc, ι_sigmaSubcomplexXIso_hom_assoc]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  exact (DirectSum.telescopeSum_lof (N := fun n ↦ (N n).N i) n x).symm

/-- The short complex `telescopeShortComplex` in degree `i` is isomorphic to the explicit
short complex of direct sums `telescopeShortComplexX`. -/
noncomputable def telescopeShortComplexMapEvalIso (i : ℤ) :
    (telescopeShortComplex N hN).map (HomologicalComplex.eval _ _ i) ≅
      telescopeShortComplexX N hN i :=
  ShortComplex.isoMk (sigmaSubcomplexXIso N i) (sigmaSubcomplexXIso N i) (Iso.refl _)
    (id_sub_telescopeShift_f_comp N hN i).symm (sigmaDesc_subcomplexι_f N i).symm

lemma telescopeShortComplexX_shortExact (hL : ∀ i (x : L.X i), ∃ n, x ∈ (N n).N i) (i : ℤ) :
    (telescopeShortComplexX N hN i).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
    exact DirectSum.ker_telescopeSum_le_range _
  · rw [ModuleCat.mono_iff_injective]
    exact DirectSum.injective_id_sub_telescopeShift _
  · rw [ModuleCat.epi_iff_surjective]
    exact DirectSum.surjective_telescopeSum (hL i)

/-- If an increasing sequence of subcomplexes `N n` exhausts `L`, then
`0 ⟶ ∐ₙ N n ⟶ ∐ₙ N n ⟶ L ⟶ 0` is short exact. -/
lemma telescopeShortComplex_shortExact (hL : ∀ i (x : L.X i), ∃ n, x ∈ (N n).N i) :
    (telescopeShortComplex N hN).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦
    ShortComplex.shortExact_of_iso (telescopeShortComplexMapEvalIso N hN i).symm
      (telescopeShortComplexX_shortExact N hN hL i)

end Telescope

section Subcomplex

/-- A subcomplex of a complex which is strictly `≤ b` is strictly `≤ b`. -/
instance isStrictlyLE_subcomplex_of_isStrictlyLE (N : L.SubcomplexFamily) (b : ℤ)
    [L.IsStrictlyLE b] : (subcomplex N).IsStrictlyLE b := by
  rw [isStrictlyLE_iff]
  intro n hn
  have := ModuleCat.isZero_iff_subsingleton.1 (L.isZero_of_isStrictlyLE b n hn)
  exact ModuleCat.isZero_iff_subsingleton.2 (inferInstanceAs (Subsingleton (N.N n)))

/-- A complex which is strictly `≥ a` and strictly `≤ b` with `b < a` is zero. -/
lemma isZero_of_isStrictlyGE_of_isStrictlyLE (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (h : b < a) [K.IsStrictlyGE a] [K.IsStrictlyLE b] : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  by_cases hi : i < a
  · exact (K.isZero_of_isStrictlyGE a i hi).eq_of_src _ _
  · exact (K.isZero_of_isStrictlyLE b i (by lia)).eq_of_src _ _

end Subcomplex

section Truncation

variable (L) in
/-- The subcomplex `σ^{≥ -m} τ^{≤ m} L` of `L`: the terms of `L` in degrees `[-m, m)`, the
cycles in degree `m`, and `0` elsewhere. -/
def truncFamily (m : ℕ) : L.SubcomplexFamily where
  N i := if -(m : ℤ) ≤ i ∧ i < m then ⊤ else
    if i = m then LinearMap.ker (L.d i (i + 1)).hom else ⊥
  map_d_le i := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases h₁ : -(m : ℤ) ≤ i + 1 ∧ i + 1 < m
    · rw [ite_eq_left h₁]
      exact Submodule.mem_top
    · rw [ite_eq_right h₁]
      by_cases h₂ : i + 1 = m
      · rw [ite_eq_left h₂, LinearMap.mem_ker, ← ModuleCat.comp_apply, L.d_comp_d]
        rfl
      · rw [ite_eq_right h₂]
        split_ifs at hx with h₃ h₄
        · lia
        · rw [LinearMap.mem_ker.1 hx]
          exact Submodule.zero_mem _
        · rw [(Submodule.mem_bot R).1 hx, map_zero]
          exact Submodule.zero_mem _

lemma mem_truncFamily_iff {m : ℕ} {i : ℤ} (x : L.X i) :
    x ∈ (truncFamily L m).N i ↔
      (-(m : ℤ) ≤ i ∧ i < m) ∨ (i = m ∧ (L.d i (i + 1)).hom x = 0) ∨ x = 0 := by
  dsimp [truncFamily]
  split_ifs with h₁ h₂
  · simp [h₁]
  · rw [LinearMap.mem_ker]
    refine ⟨fun h ↦ Or.inr (Or.inl ⟨h₂, h⟩), ?_⟩
    rintro (h | h | rfl)
    · exact absurd h h₁
    · exact h.2
    · exact map_zero _
  · simp [h₁, h₂]

lemma truncFamily_le_succ (m : ℕ) : truncFamily L m ≤ truncFamily L (m + 1) := fun i x hx ↦ by
  rw [mem_truncFamily_iff] at hx ⊢
  push_cast
  rcases hx with h | h | h
  · exact Or.inl (by lia)
  · exact Or.inl (by lia)
  · exact Or.inr (Or.inr h)

lemma exists_mem_truncFamily (i : ℤ) (x : L.X i) : ∃ m, x ∈ (truncFamily L m).N i :=
  ⟨i.natAbs + 1, (mem_truncFamily_iff x).2 (Or.inl (by lia))⟩

instance isStrictlyGE_subcomplex_truncFamily (m : ℕ) :
    (subcomplex (truncFamily L m)).IsStrictlyGE (-m) :=
  isStrictlyGE_subcomplex fun n hn ↦ by
    dsimp only [truncFamily]
    rw [ite_eq_right (by lia), ite_eq_right (by lia)]

instance isStrictlyLE_subcomplex_truncFamily (m : ℕ) :
    (subcomplex (truncFamily L m)).IsStrictlyLE m :=
  isStrictlyLE_subcomplex fun n hn ↦ by
    dsimp only [truncFamily]
    rw [ite_eq_right (by lia), ite_eq_right (by lia)]

end Truncation

section StupidTrunc

variable (L) in
/-- The stupid truncation `σ^{≥ a} L` as a family of submodules: the terms of `L` in degrees
`≥ a`, and `0` below. -/
def stupidTruncGEFamily (a : ℤ) : L.SubcomplexFamily where
  N n := if a ≤ n then ⊤ else ⊥
  map_d_le n := by
    by_cases h : a ≤ n
    · simp [h, show a ≤ n + 1 by lia]
    · simp [h]

lemma mem_stupidTruncGEFamily_iff {a i : ℤ} (x : L.X i) :
    x ∈ (stupidTruncGEFamily L a).N i ↔ a ≤ i ∨ x = 0 := by
  by_cases h : a ≤ i <;> simp [stupidTruncGEFamily, h]

lemma stupidTruncGEFamily_le_of_le {a b : ℤ} (h : a ≤ b) :
    stupidTruncGEFamily L b ≤ stupidTruncGEFamily L a := fun i x hx ↦ by
  rw [mem_stupidTruncGEFamily_iff] at hx ⊢
  lia

lemma isIso_subcomplexι_stupidTruncGEFamily_f {a i : ℤ} (h : a ≤ i ∨ IsZero (L.X i)) :
    IsIso ((subcomplexι (stupidTruncGEFamily L a)).f i) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨injective_subcomplexι_f _ i, fun y ↦ ⟨⟨y, (mem_stupidTruncGEFamily_iff y).2 ?_⟩, rfl⟩⟩
  refine h.imp_right fun h ↦ ?_
  have := ModuleCat.isZero_iff_subsingleton.1 h
  exact Subsingleton.elim _ _

/-- A complex which is strictly `≥ a` is isomorphic to its stupid truncation `σ^{≥ a}`. -/
instance isIso_subcomplexι_stupidTruncGEFamily (a : ℤ) [L.IsStrictlyGE a] :
    IsIso (subcomplexι (stupidTruncGEFamily L a)) := by
  have (i : ℤ) : IsIso ((subcomplexι (stupidTruncGEFamily L a)).f i) := by
    by_cases h : a ≤ i
    · exact isIso_subcomplexι_stupidTruncGEFamily_f (Or.inl h)
    · exact isIso_subcomplexι_stupidTruncGEFamily_f (Or.inr (L.isZero_of_isStrictlyGE a i))
  exact HomologicalComplex.Hom.isIso_of_components _

instance isStrictlyGE_subcomplex_stupidTruncGEFamily (a : ℤ) :
    (subcomplex (stupidTruncGEFamily L a)).IsStrictlyGE a :=
  isStrictlyGE_subcomplex fun n hn ↦ ite_eq_right (by lia)

instance projective_subcomplex_stupidTruncGEFamily_X [∀ i, Projective (L.X i)] (a i : ℤ) :
    Projective ((subcomplex (stupidTruncGEFamily L a)).X i) := by
  by_cases h : a ≤ i
  · have := isIso_subcomplexι_stupidTruncGEFamily_f (L := L) (Or.inl h)
    exact Projective.of_iso (asIso ((subcomplexι (stupidTruncGEFamily L a)).f i)).symm
      inferInstance
  · exact ((subcomplex (stupidTruncGEFamily L a)).isZero_of_isStrictlyGE a i).projective

variable (L) in
/-- The short complex `σ^{≥ a + 1} L ⟶ σ^{≥ a} L ⟶ Lᵃ[-a]`. -/
@[simps]
noncomputable def stupidTruncShortComplex (a : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) where
  X₁ := subcomplex (stupidTruncGEFamily L (a + 1))
  X₂ := subcomplex (stupidTruncGEFamily L a)
  X₃ := (HomologicalComplex.single _ (.up ℤ) a).obj (L.X a)
  f := subcomplexMap (stupidTruncGEFamily_le_of_le (by lia))
  g := HomologicalComplex.mkHomToSingle
    (ModuleCat.ofHom ((stupidTruncGEFamily L a).N a).subtype) fun i hi ↦ by
      obtain rfl : a = i + 1 := hi.symm
      ext x
      obtain rfl : x = 0 := Subtype.ext (by
        simpa using (mem_stupidTruncGEFamily_iff (a := i + 1) x.1).1 x.2)
      simp
  zero := by
    refine HomologicalComplex.to_single_hom_ext ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f]
    ext x
    obtain ⟨x, hx⟩ := x
    rw [mem_stupidTruncGEFamily_iff] at hx
    obtain rfl : x = 0 := by lia
    exact map_zero (HomologicalComplex.singleObjXSelf (.up ℤ) a (L.X a)).inv.hom

/-- The short complex `σ^{≥ a + 1} L ⟶ σ^{≥ a} L ⟶ Lᵃ[-a]` is short exact. -/
lemma stupidTruncShortComplex_shortExact (a : ℤ) : (stupidTruncShortComplex L a).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    rintro ⟨x, hx'⟩ hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [mem_stupidTruncGEFamily_iff] at hx' ⊢
    by_cases hi : i = a
    · subst hi
      right
      simp only [ShortComplex.map_g, HomologicalComplex.eval_map, stupidTruncShortComplex_g,
        HomologicalComplex.mkHomToSingle_f, ModuleCat.comp_apply] at hx
      have := congr((HomologicalComplex.singleObjXSelf (.up ℤ) i (L.X i)).hom $hx)
      rw [map_zero] at this
      exact (Iso.inv_hom_id_apply (HomologicalComplex.singleObjXSelf (.up ℤ) i (L.X i)) x).symm
        |>.trans this
    · lia
  · rw [ModuleCat.mono_iff_injective]
    exact Submodule.inclusion_injective (stupidTruncGEFamily_le_of_le (by lia) i)
  · by_cases hi : i = a
    · subst hi
      rw [ModuleCat.epi_iff_surjective]
      intro y
      refine ⟨⟨(HomologicalComplex.singleObjXSelf (.up ℤ) i (L.X i)).hom y, ?_⟩, ?_⟩
      · rw [mem_stupidTruncGEFamily_iff]
        exact Or.inl le_rfl
      · simp only [ShortComplex.map_g, HomologicalComplex.eval_map, stupidTruncShortComplex_g,
          HomologicalComplex.mkHomToSingle_f]
        exact Iso.hom_inv_id_apply (HomologicalComplex.singleObjXSelf (.up ℤ) i (L.X i)) y
    · exact epi_of_target_iso_zero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) _ (L.X a) _ hi).isoZero

end StupidTrunc

end CochainComplex
