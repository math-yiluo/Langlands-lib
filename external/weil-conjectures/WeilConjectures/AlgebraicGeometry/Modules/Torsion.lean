/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The torsion subsheaf of an `𝒪_X`-module

A section `s` of an `𝒪_X`-module `M` over an open `U` is a *torsion section* if it vanishes on a
dense open subset of `U`. The torsion sections form a subsheaf `M_tors ⊆ M`
(`AlgebraicGeometry.Scheme.Modules.torsion`). On an integral scheme `X` a nonempty open is dense,
so a section is torsion if and only if its germ at the generic point vanishes: `M_tors` is the
kernel of `M → M_η`. Over an affine open `U` with `Γ(X, U)` a domain, the torsion sections of a
quasi-coherent `M` are exactly the elements of `Γ(M, U)` killed by a nonzero function
(`AlgebraicGeometry.Scheme.Modules.isTorsionSection_iff_mem_torsion`), and on an irreducible
scheme `M_tors` is quasi-coherent if `M` is
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_torsion`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsTorsionSection`: sections vanishing on a dense open.
- `AlgebraicGeometry.Scheme.Modules.torsion`: the torsion subsheaf `M_tors`.
- `AlgebraicGeometry.Scheme.Modules.torsionι`: its inclusion `M_tors ⟶ M`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- A section `s` of `M` over `U` is a *torsion section* if it vanishes on a dense open subset
`V` of `U`. On an integral scheme this means that its germ at the generic point vanishes. -/
def IsTorsionSection {U : X.Opens} (s : Γ(M, U)) : Prop :=
  ∃ (V : X.Opens) (h : V ≤ U), (U : Set X) ⊆ closure (V : Set X) ∧
    M.presheaf.map (homOfLE h).op s = 0

variable {M}

/-- A section of a sheaf of modules which vanishes locally vanishes. -/
lemma eq_zero_of_forall_exists {U : X.Opens} (s : Γ(M, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ M.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  let S : Sieve U :=
    { arrows := fun _ f ↦ M.presheaf.map f.op s = 0
      downward_closed := fun {_ _} f hf g ↦ by
        dsimp only at hf ⊢
        rw [← presheaf_map_map_apply, hf, map_zero] }
  have hS : S ∈ Opens.grothendieckTopology X U := fun x hx ↦ by
    obtain ⟨V, hV, hxV, hs⟩ := h x hx
    exact ⟨V, homOfLE hV, hs, hxV⟩
  refine (M.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W f hf ↦ ?_
  refine hf.trans ?_
  exact (map_zero (M.presheaf.map f.op).hom).symm

lemma isTorsionSection_zero (U : X.Opens) : IsTorsionSection M (0 : Γ(M, U)) :=
  ⟨U, le_rfl, subset_closure, map_zero _⟩

/-- The restriction of a torsion section is a torsion section. -/
lemma IsTorsionSection.map {U W : X.Opens} {s : Γ(M, U)} (hs : IsTorsionSection M s)
    (hW : W ≤ U) : IsTorsionSection M (M.presheaf.map (homOfLE hW).op s) := by
  obtain ⟨V, hV, hdense, hs⟩ := hs
  refine ⟨V ⊓ W, inf_le_right, fun x hx ↦ ?_, ?_⟩
  · have : (W : Set X) ∩ closure (V : Set X) ⊆ closure ((W : Set X) ∩ V) :=
      W.isOpen.inter_closure
    have h := this ⟨hx, hdense (hW hx)⟩
    rwa [Set.inter_comm] at h
  · rw [presheaf_map_homOfLE_map_homOfLE,
      ← presheaf_map_homOfLE_map_homOfLE (U := U) hV inf_le_left, hs, map_zero]

lemma IsTorsionSection.add {U : X.Opens} {s t : Γ(M, U)} (hs : IsTorsionSection M s)
    (ht : IsTorsionSection M t) : IsTorsionSection M (s + t) := by
  obtain ⟨V₁, h₁, hd₁, hs⟩ := hs
  obtain ⟨V₂, h₂, hd₂, ht⟩ := ht
  refine ⟨V₁ ⊓ V₂, inf_le_left.trans h₁, fun x hx ↦ ?_, ?_⟩
  · have hsub : (V₁ : Set X) ⊆ closure ((V₁ : Set X) ∩ V₂) := fun y hy ↦
      V₁.isOpen.inter_closure ⟨hy, hd₂ (h₁ hy)⟩
    exact closure_minimal hsub isClosed_closure (hd₁ hx)
  · rw [map_add, ← presheaf_map_homOfLE_map_homOfLE h₁ inf_le_left,
      ← presheaf_map_homOfLE_map_homOfLE h₂ inf_le_right, hs, ht, map_zero, map_zero, add_zero]

lemma IsTorsionSection.smul {U : X.Opens} {s : Γ(M, U)} (hs : IsTorsionSection M s)
    (a : Γ(X, U)) : IsTorsionSection M (a • s) := by
  obtain ⟨V, hV, hd, hs⟩ := hs
  refine ⟨V, hV, hd, ?_⟩
  rw [Modules.map_smul, hs, smul_zero]

/-- **Being a torsion section is local.** -/
lemma isTorsionSection_of_forall_exists {U : X.Opens} (s : Γ(M, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      IsTorsionSection M (M.presheaf.map (homOfLE hV).op s)) :
    IsTorsionSection M s := by
  classical
  choose V hV hxV hs using h
  choose O hO hd ho using hs
  let O' : X.Opens := ⨆ x : U, O x.1 x.2
  have hO' : O' ≤ U := iSup_le fun x ↦ (hO x.1 x.2).trans (hV x.1 x.2)
  refine ⟨O', hO', fun x hx ↦ ?_, ?_⟩
  · exact closure_mono (show (O x hx : Set X) ⊆ O' from le_iSup (fun x : U ↦ O x.1 x.2) ⟨x, hx⟩)
      (hd x hx (hxV x hx))
  · refine eq_zero_of_forall_exists _ fun y hy ↦ ?_
    obtain ⟨⟨x, hx⟩, hyx⟩ := Opens.mem_iSup.mp hy
    refine ⟨O x hx, le_iSup (fun x : U ↦ O x.1 x.2) ⟨x, hx⟩, hyx, ?_⟩
    rw [presheaf_map_homOfLE_map_homOfLE,
      ← presheaf_map_homOfLE_map_homOfLE (hV x hx) (hO x hx), ho x hx]

variable (M) in
/-- The submodule of torsion sections of `Γ(M, U)`. -/
def torsionSections (U : X.Opens) : Submodule Γ(X, U) Γ(M, U) where
  carrier := {s | IsTorsionSection M s}
  zero_mem' := isTorsionSection_zero U
  add_mem' := IsTorsionSection.add
  smul_mem' a _ hs := IsTorsionSection.smul hs a

variable (M) in
/-- The presheaf of torsion sections, as a subpresheaf of modules of `M`. -/
def torsionSubmodule : M.val.Submodule where
  obj U := torsionSections M U.unop
  map {U V} f s hs := by
    have h := IsTorsionSection.map (M := M) hs f.unop.le
    exact h

lemma isSheaf_torsionSubmodule :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (torsionSubmodule M).toPresheafOfModules.presheaf := by
  refine (Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X) _
    (CategoryTheory.forget AddCommGrpCat.{u})).mpr ((isSheaf_iff_isSheaf_of_type _ _).mpr ?_)
  intro U S hS x hx
  have hM := M.isSheaf_presheaf_comp_forget _ hS
  let y : Presieve.FamilyOfElements (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) S.arrows :=
    fun V f hf ↦ (x f hf).1
  have hy : y.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congrArg Subtype.val (hx g₁ g₂ h₁ h₂ w)
  let s := hM.amalgamate y hy
  have hs : ∀ ⦃V : X.Opens⦄ (f : V ⟶ U) (hf : S.arrows f), M.presheaf.map f.op s = (x f hf).1 :=
    fun V f hf ↦ hM.valid_glue hy f hf
  have hmem : IsTorsionSection M s := by
    refine isTorsionSection_of_forall_exists s fun z hz ↦ ?_
    obtain ⟨V, f, hf, hzV⟩ := hS z hz
    refine ⟨V, f.le, hzV, ?_⟩
    have := hs f hf
    rw [show homOfLE f.le = f from rfl, this]
    exact (x f hf).2
  refine ⟨⟨s, hmem⟩, fun V f hf ↦ Subtype.ext (hs f hf), fun t ht ↦ Subtype.ext ?_⟩
  refine hM.isSeparatedFor.ext fun V f hf ↦ ?_
  refine Eq.trans ?_ (hs f hf).symm
  exact congrArg Subtype.val (ht f hf)

variable (M) in
/-- **The torsion subsheaf** `M_tors ⊆ M`: the sheaf of sections of `M` which vanish on a dense
open subset of their domain. On an integral scheme it is the kernel of `M → M_η`, `η` the
generic point. -/
noncomputable def torsion : X.Modules where
  val := (torsionSubmodule M).toPresheafOfModules
  isSheaf := isSheaf_torsionSubmodule

variable (M) in
/-- The inclusion `M_tors ⟶ M` of the torsion subsheaf. -/
noncomputable def torsionι : torsion M ⟶ M :=
  ⟨(torsionSubmodule M).ι⟩

lemma torsionι_app_apply {U : X.Opens} (s : Γ(torsion M, U)) :
    (torsionι M).app U s = s.1 :=
  rfl

lemma injective_torsionι_app (U : X.Opens) : Function.Injective ((torsionι M).app U) :=
  fun _ _ h ↦ Subtype.ext h

lemma mem_range_torsionι_app_iff {U : X.Opens} (s : Γ(M, U)) :
    s ∈ Set.range ((torsionι M).app U) ↔ IsTorsionSection M s :=
  ⟨fun ⟨t, ht⟩ ↦ ht ▸ t.2, fun h ↦ ⟨⟨s, h⟩, rfl⟩⟩

instance : Mono (torsionι M) :=
  have : Mono ((SheafOfModules.forget _).map (torsionι M)) :=
    inferInstanceAs (Mono (torsionSubmodule M).ι)
  Functor.mono_of_mono_map (SheafOfModules.forget _) this

variable (M) in
/-- The torsion-free quotient `M / M_tors` of `M`. On a smooth curve it is locally free of rank
`rk M` for coherent `M`. -/
noncomputable def torsionQuotient : X.Modules :=
  cokernel (torsionι M)

variable (M) in
/-- The projection `M ⟶ M / M_tors`. -/
noncomputable def torsionπ : M ⟶ torsionQuotient M :=
  cokernel.π (torsionι M)

variable (M) in
/-- The short exact sequence `0 ⟶ M_tors ⟶ M ⟶ M / M_tors ⟶ 0`. -/
noncomputable def torsionShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (torsionι M) (torsionπ M) (cokernel.condition _)

variable (M) in
lemma shortExact_torsionShortComplex : (torsionShortComplex M).ShortExact :=
  .mk' (ShortComplex.exact_cokernel _) (inferInstanceAs (Mono (torsionι M)))
    (inferInstanceAs (Epi (cokernel.π _)))

lemma torsion_presheaf_map_val {U V : X.Opens} (i : V ⟶ U) (s : Γ(torsion M, U)) :
    ((torsion M).presheaf.map i.op s).1 = M.presheaf.map i.op s.1 :=
  rfl

lemma torsion_smul_val {U : X.Opens} (a : Γ(X, U)) (s : Γ(torsion M, U)) :
    (a • s).1 = a • s.1 :=
  rfl

section Irreducible

variable [IrreducibleSpace X]

/-- On an irreducible scheme, a section vanishing on a nonempty open is a torsion section. -/
lemma isTorsionSection_of_presheaf_map_eq_zero {U V : X.Opens} (hV : V ≤ U)
    (hne : (V : Set X).Nonempty) {s : Γ(M, U)} (hs : M.presheaf.map (homOfLE hV).op s = 0) :
    IsTorsionSection M s :=
  ⟨V, hV, fun _ _ ↦ by rw [(V.isOpen.dense hne).closure_eq]; trivial, hs⟩

/-- **Torsion sections over an affine open.** Let `X` be an irreducible reduced scheme and `M` a
quasi-coherent `𝒪_X`-module. A section `s` of `M` over a nonempty affine open `W` is a torsion
section if and only if `a • s = 0` for some nonzero `a ∈ Γ(X, W)`. -/
lemma isTorsionSection_iff_exists_smul_eq_zero [IsReduced X]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] {W : X.Opens} (hW : IsAffineOpen W)
    (hne : (W : Set X).Nonempty) (s : Γ(M, W)) :
    IsTorsionSection M s ↔ ∃ a : Γ(X, W), a ≠ 0 ∧ a • s = 0 := by
  constructor
  · rintro ⟨V, hV, hd, hs⟩
    obtain ⟨x, hx⟩ := hne
    have hVne : (V : Set X).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := hd hx
      rw [h, closure_empty] at this
      exact this
    obtain ⟨y, hy⟩ := hVne
    obtain ⟨f, hfV, hyf⟩ := hW.exists_basicOpen_le ⟨y, hy⟩ (hV hy)
    have h0 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op s = 0 := by
      rw [← presheaf_map_homOfLE_map_homOfLE hV hfV, hs, map_zero]
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen M hW f s h0
    refine ⟨f ^ (n + 1), fun h ↦ ?_, ?_⟩
    · have := X.basicOpen_pow f (Nat.succ_pos n)
      rw [h, Scheme.basicOpen_zero] at this
      rw [← this] at hyf
      exact hyf
    · rw [pow_succ', mul_smul, hn, smul_zero]
  · rintro ⟨a, ha, hs⟩
    have hne' : (X.basicOpen a : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact ha ((AlgebraicGeometry.basicOpen_eq_bot_iff a).mp (SetLike.coe_injective (h.trans rfl)))
    refine isTorsionSection_of_presheaf_map_eq_zero (X.basicOpen_le a) hne' ?_
    obtain ⟨b, hb⟩ : ∃ b : Γ(X, X.basicOpen a),
        b * X.presheaf.map (homOfLE (X.basicOpen_le a)).op a = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen a).exists_left_inv
    have h := congrArg (M.presheaf.map (homOfLE (X.basicOpen_le a)).op) hs
    rw [Modules.map_smul, map_zero] at h
    have h' := congrArg (b • ·) h
    simp only [smul_zero, ← mul_smul] at h'
    rw [show b * _ = 1 from hb, one_smul] at h'
    exact h'

/-- **The torsion subsheaf of a quasi-coherent module on an irreducible scheme is
quasi-coherent.** This is checked with the criterion
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_forall_isAffineOpen`: if `s` is a torsion
section over `D(f) ⊆ W`, a lift of `f^n s` to `W` vanishes on a nonempty open, hence on a dense
open. -/
instance isQuasicoherent_torsion [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsion M) := by
  refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW f s ↦ ?_) (fun W hW f t ht ↦ ?_)
  · by_cases hD : (X.basicOpen f : Set X).Nonempty
    · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen M hW f s.1
      have hts : IsTorsionSection M (M.presheaf.map (homOfLE (X.basicOpen_le f)).op t) := by
        rw [ht]
        exact s.2.smul _
      obtain ⟨V, hV, hd, hV0⟩ := hts
      have hVne : (V : Set X).Nonempty := by
        obtain ⟨x, hx⟩ := hD
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty] at h
        have := hd hx
        rw [h, closure_empty] at this
        exact this
      have htt : IsTorsionSection M t := by
        refine isTorsionSection_of_presheaf_map_eq_zero (hV.trans (X.basicOpen_le f)) hVne ?_
        rw [← presheaf_map_homOfLE_map_homOfLE (X.basicOpen_le f) hV, hV0]
      exact ⟨n, ⟨t, htt⟩, Subtype.ext ht⟩
    · have hs : s = 0 := eq_zero_of_forall_exists s fun x hx ↦ absurd ⟨x, hx⟩ hD
      exact ⟨0, 0, by rw [hs, smul_zero, map_zero]⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen M hW f t.1
      (congrArg Subtype.val ht)
    exact ⟨n, Subtype.ext hn⟩

end Irreducible

end AlgebraicGeometry.Scheme.Modules
