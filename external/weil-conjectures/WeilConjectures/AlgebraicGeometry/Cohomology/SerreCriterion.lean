/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType

/-!
# Serre's criterion for affineness

A quasi-compact quasi-separated scheme `X` with `H¹(X, ℐ) = 0` for every quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_X` of finite type is affine (Stacks 01XF).

## Strategy

We follow Stacks 01XF, phrased in terms of the restriction maps `Γ(X, 𝒪_X) → Γ(V(J), 𝒪_{V(J)})`
to closed subschemes instead of cohomology of non-ideal sheaves.

1. If `H¹(X, J) = 0`, the long exact sequence of `0 ⟶ J ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0` shows that
   `Γ(X, 𝒪_X) → Γ(V(J), 𝒪_{V(J)})` is surjective
   (`surjective_subschemeι_appTop_of_subsingleton_H_one`).
2. Surjectivity for all ideal sheaves of finite type implies it for all quasi-coherent ideal
   sheaves (`surjective_subschemeι_appTop_of_ofFiniteType`): lift a section of `𝒪_{V(J)}` on a
   finite affine cover, collect the differences of the lifts in a finite-type subsheaf `K ≤ J`,
   glue the lifts on `V(K)` and lift the glued section.
3. Every closed point `x` has a neighbourhood `X_f` contained in a given open `U ∋ x`: lift the
   idempotent of `V(J)`, `V(J) = (X ∖ U) ⊔ {x}`, which is `1` at `x` and `0` on `X ∖ U`
   (`Scheme.exists_basicOpen_le_of_isClosed`).
4. Global functions `f₁, …, fₙ` with `X = ⋃ X_{fᵢ}` generate the unit ideal: by induction on `n`,
   working on the closed subscheme `V(f₁)` (`Scheme.span_eq_top_of_forall_mem_basicOpen`).

Since closed points are dense in every closed subset of the quasi-compact scheme `X`, step 3
provides finitely many `fᵢ` with `X_{fᵢ}` affine covering `X`, and `X` is affine by step 4 and
`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`.

## Main statements

- `AlgebraicGeometry.isAffine_of_subsingleton_H_one`: Serre's criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- If `H¹(X, J) = 0`, then every global section of the closed subscheme `V(J)` lifts to a global
function on `X`: this is the long exact cohomology sequence of
`0 ⟶ J ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0` in degree `0`.

(blueprint: `pqf-lem-serre-criterion`) -/
theorem surjective_subschemeι_appTop_of_subsingleton_H_one (J : X.IdealSheafData)
    [Subsingleton (J.toModules.H 1)] : Function.Surjective J.subschemeι.appTop := by
  intro y
  have hy : (Modules.H.zeroLinearEquiv J.shortComplex.X₃).symm y ∈
      (Modules.H.δ J.shortExact_shortComplex 0).ker :=
    Subsingleton.elim (α := J.toModules.H 1) _ _
  rw [Modules.H.ker_δ_eq_range_map_g] at hy
  obtain ⟨z, hz⟩ := hy
  refine ⟨Modules.H.zeroLinearEquiv J.shortComplex.X₂ z, ?_⟩
  refine (Sheaf.H.equiv₀_naturality isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map J.shortComplex.g) z).trans ?_
  exact (congrArg (Modules.H.zeroLinearEquiv J.shortComplex.X₃) hz).trans
    ((Modules.H.zeroLinearEquiv J.shortComplex.X₃).apply_symm_apply y)

/-- **Reduction to ideal sheaves of finite type.** Let `X` be quasi-compact and
quasi-separated, and suppose that `Γ(X, 𝒪_X) → Γ(V(K), 𝒪_{V(K)})` is surjective for every ideal
sheaf `K` of finite type. Then it is surjective for every quasi-coherent ideal sheaf `J`.

A section `s` over `V(J)` lifts to sections `e a` of `𝒪_X` over the members `U a` of a finite
affine cover. The differences `e a - e b` are sections of `J` over the quasi-compact opens
`U a ⊓ U b`, so they are sections of a single finite-type subsheaf `K ≤ J`. Modulo `K` the
`e a` glue to a section over `V(K)`, which lifts to a global function `f`; then `f` restricts to
`s` on `V(J)`, since `f - e a` is a section of `K ≤ J` over `U a`.

(blueprint: `pqf-lem-serre-criterion`) -/
theorem surjective_subschemeι_appTop_of_ofFiniteType [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ K : X.IdealSheafData, K.ofFiniteType → Function.Surjective K.subschemeι.appTop)
    (J : X.IdealSheafData) : Function.Surjective J.subschemeι.appTop := by
  intro s
  obtain ⟨Us, hUs, hfin, hXUs⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  have := hfin.to_subtype
  have hcov : ⊤ ≤ ⨆ a : Us, a.1 := by rw [hXUs, sSup_eq_iSup']
  have hlift (a : Us) : ∃ e : Γ(X, a.1),
      J.subschemeι.app a.1 e = J.subscheme.presheaf.map (homOfLE le_top).op s :=
    J.subschemeι_app_surjective ⟨a.1, hUs a.2⟩ _
  choose e he using hlift
  have hd (p : Us × Us) : X.presheaf.map (homOfLE inf_le_left).op (e p.1) -
      X.presheaf.map (homOfLE inf_le_right).op (e p.2) ∈ J.idealOfOpens (p.1.1 ⊓ p.2.1) := by
    rw [mem_idealOfOpens_iff, map_sub, sub_eq_zero,
      J.subschemeι.app_map_apply _ (homOfLE (J.subschemeι.preimage_mono inf_le_left)), he,
      J.subschemeι.app_map_apply _ (homOfLE (J.subschemeι.preimage_mono inf_le_right)), he,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  have hcpt (p : Us × Us) : IsCompact ((p.1.1 ⊓ p.2.1 : X.Opens) : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ p.1.1.2 (hUs p.1.2).isCompact p.2.1.2
      (hUs p.2.2).isCompact
  choose K hKJ hK hdK using fun p ↦ J.exists_ofFiniteType_le_mem_idealOfOpens (hcpt p) (hd p)
  set K' : X.IdealSheafData := ⨆ p, K p
  let ι' := K'.subschemeι
  have hcompat : TopCat.Presheaf.IsCompatible K'.subscheme.sheaf.obj
      (fun a : Us ↦ ι' ⁻¹ᵁ a.1) (fun a ↦ ι'.app a.1 (e a)) := by
    intro a b
    refine (ι'.app_map_apply (homOfLE inf_le_left) _ (e a)).symm.trans
      (Eq.trans ?_ (ι'.app_map_apply (homOfLE inf_le_right) _ (e b)))
    rw [← sub_eq_zero, ← map_sub, ← mem_idealOfOpens_iff]
    exact idealOfOpens_mono_finiteType (le_iSup K (a, b)) _ (hdK (a, b))
  obtain ⟨g, hg, -⟩ := K'.subscheme.sheaf.existsUnique_gluing' (fun a : Us ↦ ι' ⁻¹ᵁ a.1) ⊤
    (fun a ↦ homOfLE le_top) (by rw [← Scheme.Hom.preimage_iSup]; exact ι'.preimage_mono hcov)
    _ hcompat
  obtain ⟨f, hf⟩ := h K' (ofFiniteType_iSup hK) g
  refine ⟨f, J.subscheme.sheaf.eq_of_locally_eq' (fun a : Us ↦ J.subschemeι ⁻¹ᵁ a.1) ⊤
    (fun a ↦ homOfLE le_top)
    (by rw [← Scheme.Hom.preimage_iSup]; exact J.subschemeι.preimage_mono hcov) _ _ fun a ↦ ?_⟩
  have hfa : X.presheaf.map (homOfLE le_top).op f - e a ∈ K'.idealOfOpens a.1 := by
    rw [mem_idealOfOpens_iff, map_sub, sub_eq_zero, ι'.app_map_apply _ (homOfLE le_top)]
    exact (congrArg _ hf).trans (hg a)
  have := idealOfOpens_mono_finiteType (iSup_le hKJ) _ hfa
  rw [mem_idealOfOpens_iff, map_sub, sub_eq_zero,
    J.subschemeι.app_map_apply _ (homOfLE le_top), he] at this
  exact this

end Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- If global functions lift along the closed subscheme `V(J)` for every ideal sheaf `J`, they
lift along every closed immersion, since a closed immersion `i` factors as the isomorphism
`i.toImage` followed by the inclusion of the closed subscheme cut out by its kernel. -/
lemma Scheme.surjective_appTop_of_isClosedImmersion
    (hX : ∀ J : X.IdealSheafData, Function.Surjective J.subschemeι.appTop) {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : Function.Surjective i.appTop := by
  rw [← i.toImage_imageι, Scheme.Hom.comp_appTop]
  intro y
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.toImage.app ⊤)).2 y
  obtain ⟨b, rfl⟩ := hX i.ker a
  exact ⟨b, ConcreteCategory.comp_apply _ _ _⟩

/-- On a quasi-compact quasi-separated scheme, if `X_h ⊆ X_g` for global functions `g` and `h`,
then a power of `h` is a multiple of `g`: `g` becomes a unit in `Γ(X_h, 𝒪_X) = Γ(X, 𝒪_X)_h`. -/
lemma Scheme.mem_radical_span_singleton_of_basicOpen_le [CompactSpace X]
    [QuasiSeparatedSpace X] {g h : Γ(X, ⊤)} (hle : X.basicOpen h ≤ X.basicOpen g) :
    h ∈ (Ideal.span {g}).radical := by
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ h
  have hunit : IsUnit (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen h) g) := by
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) :=
      RingedSpace.isUnit_res_basicOpen _ g
    have := hu.map (X.presheaf.map (homOfLE hle).op).hom
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
    exact this
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff h).1 hunit
  exact ⟨n, Ideal.mem_span_singleton.2 hn⟩

/-- Let `Y` be a quasi-compact quasi-separated scheme along all of whose closed immersions global
functions lift. If the basic opens `Y_{f i}`, `i ∈ s`, cover `Y`, then the `f i` generate the unit
ideal of `Γ(Y, 𝒪_Y)`.

By induction on `s`: the remaining functions cover the closed subscheme `V(f i₀)`, so by
induction they generate the unit ideal there; lifting a relation `1 = ∑ cᵢ fᵢ` from `V(f i₀)`
to `Y` leaves an error term `h` vanishing on `V(f i₀)`, hence with `Y_h ⊆ Y_{f i₀}`, so that a
power of `h` is a multiple of `f i₀`.

(blueprint: `pqf-lem-serre-criterion`) -/
theorem Scheme.span_eq_top_of_forall_mem_basicOpen {ι : Type*} (s : Finset ι) :
    ∀ (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y],
      (∀ {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i], Function.Surjective i.appTop) →
      ∀ f : ι → Γ(Y, ⊤), (∀ y : Y, ∃ i ∈ s, y ∈ Y.basicOpen (f i)) →
        Ideal.span (f '' s) = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro Y _ _ _ f hf
    have : IsEmpty Y := ⟨fun y ↦ by simpa using hf y⟩
    rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Y, ⊤)) 0]
    exact zero_mem _
  | insert i₀ s hi₀ ih =>
    intro Y _ _ hY f hf
    set J := Scheme.IdealSheafData.ofIdealTop (Ideal.span {f i₀})
    have hJ (y : Y) : y ∈ Set.range J.subschemeι ↔ y ∉ Y.basicOpen (f i₀) := by
      rw [J.range_subschemeι, IdealSheafData.coe_support_ofIdealTop, zeroLocus_span,
        mem_zeroLocus_iff]
      simp
    have hY' {Z : Scheme.{u}} (i : Z ⟶ J.subscheme) [IsClosedImmersion i] :
        Function.Surjective i.appTop := by
      have := hY (i ≫ J.subschemeι)
      rw [Scheme.Hom.comp_appTop] at this
      exact Function.Surjective.of_comp this
    have key := ih J.subscheme hY' (fun i ↦ J.subschemeι.appTop (f i)) fun y ↦ by
      obtain ⟨i, hi, hyi⟩ := hf (J.subschemeι y)
      have hii₀ : i ≠ i₀ := by
        rintro rfl
        exact (hJ _).1 ⟨y, rfl⟩ hyi
      refine ⟨i, (Finset.mem_insert.1 hi).resolve_left hii₀, ?_⟩
      rw [← Scheme.preimage_basicOpen_top]
      exact hyi
    rw [← Set.image_image (g := J.subschemeι.appTop), ← Ideal.map_span] at key
    obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ (hY J.subschemeι)).1
      (key.symm ▸ Submodule.mem_top : (1 : Γ(J.subscheme, ⊤)) ∈ _)
    have hle : Y.basicOpen (1 - a) ≤ Y.basicOpen (f i₀) := by
      intro y hy
      by_contra hn
      obtain ⟨y', rfl⟩ := (hJ y).2 hn
      have : y' ∈ J.subscheme.basicOpen (J.subschemeι.appTop (1 - a)) := by
        rw [← Scheme.preimage_basicOpen_top]
        exact hy
      rw [map_sub, map_one, ha1, sub_self, Scheme.basicOpen_zero] at this
      exact this
    have hrad := mem_radical_span_singleton_of_basicOpen_le hle
    rw [← Ideal.radical_eq_top, Ideal.eq_top_iff_one, ← add_sub_cancel a 1]
    refine add_mem (Ideal.le_radical (Ideal.span_mono ?_ ha)) (Ideal.radical_mono
      (Ideal.span_mono ?_) hrad)
    · exact Set.image_mono (by simp)
    · simp

/-- Suppose that global functions lift along every closed subscheme of `X`. Then every closed
point `x` of an open `U` has a basic open neighbourhood `X_f ⊆ U`.

Let `V(J)` be the reduced closed subscheme on `(X ∖ U) ∪ {x}`. It is the disjoint union of its
open subsets over `U` (which is `{x}`) and over `X ∖ {x}`, so it has a global section which is `1`
on the first and `0` on the second; any lift `f` of it satisfies `x ∈ X_f ⊆ U`.

(blueprint: `pqf-lem-serre-criterion`) -/
lemma Scheme.exists_basicOpen_le_of_isClosed
    (hX : ∀ J : X.IdealSheafData, Function.Surjective J.subschemeι.appTop) {x : X}
    (hx : IsClosed {x}) {U : X.Opens} (hxU : x ∈ U) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ X.basicOpen f ≤ U := by
  let Z : Closeds X := ⟨(U : Set X)ᶜ ∪ {x}, U.2.isClosed_compl.union hx⟩
  set J := IdealSheafData.vanishingIdeal Z
  let ι := J.subschemeι
  have hrange : Set.range ι = (U : Set X)ᶜ ∪ {x} := by
    rw [J.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let A : J.subscheme.Opens := ι ⁻¹ᵁ U
  let B : J.subscheme.Opens := ι ⁻¹ᵁ ⟨{x}ᶜ, hx.isOpen_compl⟩
  have hAB : A ⊓ B = ⊥ := by
    refine eq_bot_iff.2 fun y ⟨hyA, hyB⟩ ↦ ?_
    have hy : ι y ∈ (U : Set X)ᶜ ∪ {x} := hrange ▸ ⟨y, rfl⟩
    rcases hy with hy | hy
    · exact hy hyA
    · exact hyB hy
  have hcov : ⊤ ≤ A ⊔ B := by
    intro y _
    by_cases h : ι y = x
    · exact Or.inl (h ▸ hxU : ι y ∈ U)
    · exact Or.inr h
  have : Subsingleton Γ(J.subscheme, A ⊓ B) := by
    rw [hAB]
    infer_instance
  let e₀ : Γ(J.subscheme, A ⊔ B) := (J.subscheme.sheaf.objSupIsoProdEqLocus A B).inv
    ⟨(1, 0), Subsingleton.elim (α := Γ(J.subscheme, A ⊓ B)) _ _⟩
  set e := J.subscheme.presheaf.map (homOfLE hcov).op e₀ with he
  obtain ⟨f, hf⟩ := hX J e
  have heA : J.subscheme.presheaf.map (homOfLE le_top : A ⟶ ⊤).op e = 1 := by
    rw [he]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    exact J.subscheme.sheaf.objSupIsoProdEqLocus_inv_fst A B _
  have heB : J.subscheme.presheaf.map (homOfLE le_top : B ⟶ ⊤).op e = 0 := by
    rw [he]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    exact J.subscheme.sheaf.objSupIsoProdEqLocus_inv_snd A B _
  have hbA : A ≤ J.subscheme.basicOpen e := by
    have h := J.subscheme.basicOpen_res e (homOfLE le_top : A ⟶ ⊤).op
    rw [heA, Scheme.basicOpen_one] at h
    exact h.le.trans inf_le_right
  have hbB : B ⊓ J.subscheme.basicOpen e = ⊥ := by
    rw [← J.subscheme.basicOpen_res e (homOfLE le_top : B ⟶ ⊤).op, heB, Scheme.basicOpen_zero]
  have hpre : ι ⁻¹ᵁ X.basicOpen f = J.subscheme.basicOpen e := by
    rw [Scheme.preimage_basicOpen_top, hf]
  refine ⟨f, ?_, fun z hz ↦ ?_⟩
  · obtain ⟨y, hy⟩ : x ∈ Set.range ι := by
      rw [hrange]
      exact Or.inr rfl
    have hyA : ι y ∈ U := hy ▸ hxU
    have : y ∈ ι ⁻¹ᵁ X.basicOpen f := hpre ▸ hbA hyA
    exact hy ▸ this
  · by_contra hzU
    obtain ⟨y, rfl⟩ : z ∈ Set.range ι := by
      rw [hrange]
      exact Or.inl hzU
    have hyB : y ∈ B := fun h ↦ hzU (h ▸ hxU : ι y ∈ U)
    have hy : y ∈ J.subscheme.basicOpen e := hpre ▸ hz
    have : y ∈ B ⊓ J.subscheme.basicOpen e := ⟨hyB, hy⟩
    rw [hbB] at this
    exact this

/-- **Serre's criterion for affineness.** Let `X` be a quasi-compact quasi-separated scheme such
that `H¹(X, ℐ) = 0` for every quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` of finite type. Then `X`
is affine.

(blueprint: `pqf-lem-serre-criterion`) -/
@[stacks 01XF]
theorem isAffine_of_subsingleton_H_one (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ I : X.IdealSheafData,
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) I.toModules →
        Subsingleton (I.toModules.H 1)) :
    IsAffine X := by
  have hX : ∀ J : X.IdealSheafData, Function.Surjective J.subschemeι.appTop :=
    Scheme.IdealSheafData.surjective_subschemeι_appTop_of_ofFiniteType fun K hK ↦
      have := h K (K.isFiniteType_toModules hK)
      K.surjective_subschemeι_appTop_of_subsingleton_H_one
  have hcov (y : X) : ∃ f : Γ(X, ⊤), IsAffineOpen (X.basicOpen f) ∧ y ∈ X.basicOpen f := by
    obtain ⟨x, hx, hxc⟩ :=
      (isClosed_closure (s := {y})).exists_closed_singleton ⟨y, subset_closure rfl⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨f, hxf, hfU⟩ := Scheme.exists_basicOpen_le_of_isClosed hX hxc hxU
    refine ⟨f, ?_, ?_⟩
    · have := hU.basicOpen (X.presheaf.map (homOfLE le_top).op f)
      rwa [Scheme.basicOpen_res, inf_eq_right.2 hfU] at this
    · by_contra hy
      exact closure_minimal (Set.singleton_subset_iff.2 hy) (X.basicOpen f).2.isClosed_compl
        hx hxf
  choose g hg hyg using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (X.basicOpen (g y) : Set X))
    (fun y ↦ (X.basicOpen (g y)).2) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyg y⟩)
  have hspan := Scheme.span_eq_top_of_forall_mem_basicOpen t X
    (Scheme.surjective_appTop_of_isClosedImmersion hX) g fun y ↦ by
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
      exact ⟨i, hi, hyi⟩
  exact isAffine_of_isAffineOpen_basicOpen (g '' t) hspan (by rintro _ ⟨y, -, rfl⟩; exact hg y)

end AlgebraicGeometry
