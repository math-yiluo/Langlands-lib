/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
public import WeilConjectures.AlgebraicGeometry.Curve.QuasiProjective
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Opens of an affine Dedekind scheme are affine

Let `X` be an integral affine scheme whose ring of global sections `A` is a Dedekind domain. Every
open `U` of `X` is affine (`AlgebraicGeometry.isAffineOpen_of_isDedekindDomain`): write the
complement of `U` as the zero locus of an ideal `I` of `A`. As a fractional ideal `I` is
invertible, so `1 = ∑ aᵢ bᵢ` with `aᵢ ∈ I` and `bᵢ ∈ I⁻¹`. Each `bᵢ` is a regular function on `U`:
on the basic open `D(f)`, `f ∈ I`, it is `(bᵢ f) / f` with `bᵢ f ∈ A`. Hence the restrictions of
the elements of `I` generate the unit ideal of `Γ(X, U)`, and their basic opens `D(f)` are
affine.

In particular every open of a smooth affine curve over a field is affine, and a dense open of a
smooth geometrically connected affine curve is a smooth geometrically connected affine curve
(`AlgebraicGeometry.isAffine_of_isOpenImmersion_of_smoothOfRelativeDimension_one`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace AlgebraicGeometry

section Dedekind

variable {X : Scheme.{u}} [IsAffine X] [IsIntegral X] [IsDedekindDomain Γ(X, ⊤)]

omit [IsAffine X] [IsDedekindDomain Γ(X, ⊤)] in
/-- An element `b` of the function field such that `b f` is a global function for every `f` in
an ideal `I` with `⋃_{f ∈ I} D(f) = U` is a regular function on `U`: on `D(f)` it is
`(b f) / f`. -/
private lemma exists_germToFunctionField_eq (U : X.Opens) [Nonempty U] [Nonempty (⊤ : X.Opens)]
    (I : Ideal Γ(X, ⊤))
    (hUI : ∀ x ∈ U, ∃ f ∈ I, x ∈ X.basicOpen f) (b : X.functionField)
    (hb : ∀ f ∈ I, ∃ c : Γ(X, ⊤), algebraMap Γ(X, ⊤) X.functionField c =
      b * algebraMap Γ(X, ⊤) X.functionField f) :
    ∃ β : Γ(X, U), X.germToFunctionField U β = b := by
  classical
  let ι : Type u := {f : Γ(X, ⊤) // f ∈ I ∧ f ≠ 0}
  let V : ι → X.Opens := fun f ↦ X.basicOpen f.1
  have hV (f : ι) : Nonempty (V f) := by
    by_contra h
    have : V f = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx ↦ h ⟨⟨x, hx⟩⟩
    exact f.2.2 ((basicOpen_eq_bot_iff f.1).1 this)
  choose c hc using hb
  let s : ∀ f : ι, Γ(X, V f) := fun f ↦
    (X.presheaf.map (homOfLE (le_top : V f ≤ ⊤)).op (c f.1 f.2.1) : Γ(X, V f)) *
      (show Γ(X, V f) from (X.toRingedSpace.isUnit_res_basicOpen f.1).unit⁻¹.val)
  have hs (f : ι) : X.germToFunctionField (V f) (s f) = b := by
    have hu := (X.toRingedSpace.isUnit_res_basicOpen f.1).mul_val_inv
    have h₁ := congrArg (X.germToFunctionField (V f)) hu
    rw [map_mul, map_one] at h₁
    simp only [s, map_mul]
    have h₂ : X.germToFunctionField (V f) (X.presheaf.map (homOfLE le_top).op (c f.1 f.2.1)) =
        b * X.germToFunctionField (V f) (X.presheaf.map (homOfLE (X.basicOpen_le f.1)).op f.1) := by
      rw [Scheme.germToFunctionField_map_quasiProjective,
        Scheme.germToFunctionField_map_quasiProjective]
      exact hc f.1 f.2.1
    rw [h₂, mul_assoc]
    convert mul_one b using 2
  obtain ⟨t, ht⟩ := Scheme.exists_gluing_of_germToFunctionField_eq V s b hs
  have hle : U ≤ ⨆ i, V i := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hUI x hx
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hxf
    exact Opens.mem_iSup.2 ⟨⟨f, hf, hf0⟩, hxf⟩
  obtain ⟨x, hx⟩ := (inferInstance : Nonempty U)
  obtain ⟨f, hf, hxf⟩ := hUI x hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hxf
  let i : ι := ⟨f, hf, hf0⟩
  have : Nonempty (⨆ i, V i : X.Opens) := ⟨⟨x, hle hx⟩⟩
  refine ⟨X.presheaf.map (homOfLE hle).op t, ?_⟩
  rw [Scheme.germToFunctionField_map_quasiProjective, ← hs i, ← ht i,
    Scheme.germToFunctionField_map_quasiProjective]

/-- **Opens of an affine Dedekind scheme are affine.** If `X` is an integral affine scheme whose
ring of global sections is a Dedekind domain, then every open `U` of `X` is affine. -/
theorem isAffineOpen_of_isDedekindDomain (U : X.Opens) : IsAffineOpen U := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · exact IsAffineOpen.of_subsingleton fun x hx ↦ (hU.false ⟨x, hx⟩).elim
  have : Nonempty (⊤ : X.Opens) := by
    obtain ⟨x⟩ := hU
    exact ⟨⟨x.1, trivial⟩⟩
  obtain ⟨I, hI⟩ := (Scheme.eq_zeroLocus_of_isClosed_of_isAffine X (U : Set X)ᶜ).1
    U.isOpen.isClosed_compl
  have hIU (f) (hf : f ∈ I) : X.basicOpen f ≤ U := by
    intro x hx
    by_contra hxU
    have : x ∈ X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)) := hI ▸ hxU
    exact (X.mem_zeroLocus_iff _ x).1 this f hf hx
  have hUI (x) (hx : x ∈ U) : ∃ f ∈ I, x ∈ X.basicOpen f := by
    have : x ∉ X.zeroLocus (U := ⊤) (I : Set Γ(X, ⊤)) := hI ▸ fun h ↦ h hx
    rw [X.mem_zeroLocus_iff] at this
    simp only [not_forall, not_not, exists_prop] at this
    exact this
  have := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  have hI0 : I ≠ ⊥ := by
    obtain ⟨x⟩ := hU
    obtain ⟨f, hf, hxf⟩ := hUI x.1 x.2
    intro h
    rw [h, Ideal.mem_bot] at hf
    subst hf
    simp at hxf
  set s : Set Γ(X, U) := X.presheaf.map (homOfLE le_top).op '' I with hs
  have key : ∀ y ∈ ((I : FractionalIdeal Γ(X, ⊤)⁰ X.functionField) *
      (I : FractionalIdeal Γ(X, ⊤)⁰ X.functionField)⁻¹ : FractionalIdeal _ _),
      ∃ t ∈ Ideal.span s, X.germToFunctionField U t = y := by
    intro y hy
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hy
    refine Submodule.mul_induction_on hy (fun m hm n hn ↦ ?_) fun y₁ y₂ ⟨t₁, ht₁, e₁⟩
      ⟨t₂, ht₂, e₂⟩ ↦ ⟨t₁ + t₂, add_mem ht₁ ht₂, by rw [map_add, e₁, e₂]⟩
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
    have hn' := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI0)).1 hn
    obtain ⟨β, hβ⟩ := exists_germToFunctionField_eq U I hUI n fun f hf ↦ by
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
        (hn' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨f, hf, rfl⟩))
      exact ⟨c, hc⟩
    refine ⟨X.presheaf.map (homOfLE le_top).op a * β,
      Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ha, rfl⟩), ?_⟩
    rw [map_mul, hβ, Scheme.germToFunctionField_map_quasiProjective]
    rfl
  rw [FractionalIdeal.coe_ideal_mul_inv I hI0] at key
  obtain ⟨t, ht, ht1⟩ := key 1 (FractionalIdeal.one_mem_one _)
  have ht' : t = 1 := X.germToFunctionField_injective U (by rw [ht1, map_one])
  refine isAffineOpen_of_isAffineOpen_basicOpen U s
    ((Ideal.eq_top_iff_one _).2 (ht' ▸ ht)) ?_
  rintro _ ⟨f, hf, rfl⟩
  rw [Scheme.basicOpen_res, inf_eq_right.2 (hIU f hf)]
  exact (isAffineOpen_top X).basicOpen f

end Dedekind

section Curve

variable {k : Type u} [Field k] {U C : Scheme.{u}}

/-- **Opens of a smooth affine curve are affine.** If `C` is a connected affine scheme smooth of
relative dimension one over a field, then every open subscheme of `C` is affine: `C` is integral
and its ring of global sections is a Dedekind domain. -/
theorem isAffine_of_isOpenImmersion_of_smoothOfRelativeDimension_one (j : U ⟶ C)
    [IsOpenImmersion j] (p : C ⟶ Spec (.of k)) [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [ConnectedSpace C] : IsAffine U := by
  have := SmoothOfRelativeDimension.smooth 1 p
  have : IsCurve p :=
    { krullDim_le_one := by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension p 1 }
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsRegular.of_smooth p
  have := IsRegular.isIntegral C
  have : Nonempty (⊤ : C.Opens) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty C)
    exact ⟨⟨x, trivial⟩⟩
  have := isDedekindDomain_of_isAffineOpen p (isAffineOpen_top C)
  have : IsAffine j.opensRange := isAffineOpen_of_isDedekindDomain j.opensRange
  exact .of_isIso j.isoOpensRange.hom

end Curve

end AlgebraicGeometry
