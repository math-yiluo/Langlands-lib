/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Objects with a finite filtration whose quotients satisfy a property

Given a property `P` of objects of an abelian category `C`, `P.filtrationClosure` is the
property of admitting a finite filtration `0 = X₀ ↪ X₁ ↪ ⋯ ↪ Xₙ = X` whose successive quotients
`Xᵢ₊₁ / Xᵢ` satisfy `P`. It is defined inductively; `filtrationClosure_iff` relates it to
filtrations indexed by `Fin (n + 1)`.

If `P` is closed under isomorphisms, then `P.filtrationClosure` is closed under extensions; if
`P` is closed under subobjects (resp. quotients), so is `P.filtrationClosure`: intersect the
filtration with the subobject (resp. take the images of the filtration in the quotient).

If `P` is closed under kernels, cokernels and extensions, then in an exact sequence
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄ ⟶ X₅` whose four outer terms satisfy `P`, so does `X₃`
(`CategoryTheory.ObjectProperty.prop_X₃_of_exact`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits ZeroObject

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)

/-- The property of objects `X` of an abelian category admitting a finite filtration
`0 = X₀ ↪ X₁ ↪ ⋯ ↪ Xₙ = X` whose successive quotients satisfy `P`. -/
inductive filtrationClosure : ObjectProperty C
  | of_isZero {X : C} (hX : IsZero X) : filtrationClosure X
  | of_mono {X Y : C} (i : X ⟶ Y) [Mono i] (hX : filtrationClosure X) (hi : P (cokernel i)) :
      filtrationClosure Y

variable {P}

/-- The cokernel of the kernel of an epimorphism `g : X ⟶ Y` is `Y`. -/
noncomputable def cokernelKernelιIsoOfEpi {X Y : C} (g : X ⟶ Y) [Epi g] :
    cokernel (kernel.ι g) ≅ Y :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel g))

private lemma exact_cokernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

instance [P.IsClosedUnderIsomorphisms] : P.filtrationClosure.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    induction hX with
    | of_isZero hX => exact .of_isZero (hX.of_iso e.symm)
    | of_mono i hX hi =>
      exact .of_mono (i ≫ e.hom) hX (P.prop_of_iso (cokernelCompIsIso i e.hom).symm hi)

lemma le_filtrationClosure [P.IsClosedUnderIsomorphisms] : P ≤ P.filtrationClosure :=
  fun X hX ↦ .of_mono (0 : 0 ⟶ X) (.of_isZero (isZero_zero C))
    (P.prop_of_iso (cokernelZeroIsoTarget (X := 0)).symm hX)

instance [P.IsClosedUnderSubobjects] : P.filtrationClosure.IsClosedUnderSubobjects where
  prop_of_mono {G Y} m _ hY := by
    induction hY generalizing G with
    | of_isZero hY => exact .of_isZero (hY.of_mono m)
    | @of_mono X Y i _ hX hi ih =>
      let g := m ≫ cokernel.π i
      let t := (exact_cokernel i).lift (kernel.ι g ≫ m) (by simp [g])
      have ht : t ≫ i = kernel.ι g ≫ m := (exact_cokernel i).lift_f _ _
      have : Mono t := mono_of_mono_fac ht
      exact .of_mono (kernel.ι g) (ih t inferInstance)
        (P.prop_of_iso (Abelian.coimageIsoImage g).symm (P.prop_of_mono (Abelian.image.ι g) hi))

instance [P.IsClosedUnderQuotients] : P.filtrationClosure.IsClosedUnderQuotients where
  prop_of_epi {X H} p _ hX := by
    induction hX generalizing H with
    | of_isZero hX => exact .of_isZero (hX.of_epi p)
    | @of_mono X₀ X i _ hX₀ hi ih =>
      let f := i ≫ p
      have hf : i ≫ p ≫ cokernel.π f = 0 := by rw [← Category.assoc]; exact cokernel.condition f
      have : Epi (cokernel.desc i (p ≫ cokernel.π f) hf) :=
        epi_of_epi_fac (cokernel.π_desc i (p ≫ cokernel.π f) hf)
      exact .of_mono (Abelian.image.ι f) (ih (Abelian.factorThruImage f) inferInstance)
        (P.prop_of_iso (cokernelKernelιIsoOfEpi (cokernel.π f)).symm
          (P.prop_of_epi (cokernel.desc i (p ≫ cokernel.π f) hf) hi))

/-- The key step of the closure under extensions: if `0 ⟶ A ⟶ B ⟶ Q ⟶ 0` is exact with `A`
and `Q` admitting finite `P`-filtrations, then so does `B`; by induction on the filtration of
`Q`. -/
private lemma filtrationClosure_X₂ [P.IsClosedUnderIsomorphisms] {Q : C}
    (hQ : P.filtrationClosure Q) :
    ∀ {A B : C} (i : A ⟶ B) (p : B ⟶ Q) (w : i ≫ p = 0) [Mono i] [Epi p],
      (ShortComplex.mk i p w).Exact → P.filtrationClosure A → P.filtrationClosure B := by
  induction hQ with
  | of_isZero hQ =>
    intro A B i p w _ _ hS hA
    have : Epi i := (ShortComplex.mk i p w).exact_iff_epi (hQ.eq_of_tgt _ _) |>.1 hS
    have : IsIso i := isIso_of_mono_of_epi i
    exact P.filtrationClosure.prop_of_iso (asIso i) hA
  | @of_mono Q' Q j _ hQ' hj ih =>
    intro A B i p w _ _ hS hA
    let g := p ≫ cokernel.π j
    let ι := kernel.ι g
    let i' : A ⟶ kernel g := kernel.lift g i (by simp [g, reassoc_of% w])
    have hi' : i' ≫ ι = i := kernel.lift_ι _ _ _
    have : Mono i' := mono_of_mono_fac hi'
    let p' : kernel g ⟶ Q' := (exact_cokernel j).lift (ι ≫ p) (by simp [ι, g])
    have hp' : p' ≫ j = ι ≫ p := (exact_cokernel j).lift_f _ _
    have w' : i' ≫ p' = 0 := by
      rw [← cancel_mono j, Category.assoc, hp', reassoc_of% hi', w, zero_comp]
    have : Epi p' := by
      rw [epi_iff_surjective_up_to_refinements]
      intro T q
      obtain ⟨T', π, _, b, hb⟩ := surjective_up_to_refinements_of_epi p (q ≫ j)
      refine ⟨T', π, inferInstance, kernel.lift g b ?_, ?_⟩
      · simp [g, ← reassoc_of% hb]
      · rw [← cancel_mono j, Category.assoc, Category.assoc, hp', kernel.lift_ι_assoc, hb]
    have hS' : (ShortComplex.mk i' p' w').Exact := by
      rw [ShortComplex.exact_iff_exact_up_to_refinements] at hS ⊢
      intro T x hx
      obtain ⟨T', π, _, a, ha⟩ := hS (x ≫ ι)
        (by simpa [← hp'] using congrArg (· ≫ j) hx)
      refine ⟨T', π, inferInstance, a, ?_⟩
      rw [← cancel_mono ι]
      simpa [hi'] using ha
    exact .of_mono ι (ih i' p' w' hS' hA) (P.prop_of_iso (cokernelKernelιIsoOfEpi g).symm hj)

instance [P.IsClosedUnderIsomorphisms] : P.filtrationClosure.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    exact filtrationClosure_X₂ h₃ S.f S.g S.zero hS.exact h₁

private lemma prop_cokernel_comp [P.IsClosedUnderIsomorphisms] {X' X Y Y' : C} (a : X' ⟶ X)
    [IsIso a] (f : X ⟶ Y) (b : Y ⟶ Y') [IsIso b] (h : P (cokernel f)) :
    P (cokernel (a ≫ f ≫ b)) :=
  P.prop_of_iso (cokernelEpiComp a (f ≫ b) ≪≫ cokernelCompIsIso f b).symm h

/-- An object admits a finite filtration whose successive quotients satisfy `P` if and only if
there is a chain of monomorphisms `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G n ≅ X` whose cokernels satisfy `P`. -/
theorem filtrationClosure_iff [P.IsClosedUnderIsomorphisms] {X : C} :
    P.filtrationClosure X ↔ ∃ (n : ℕ) (G : Fin (n + 1) → C)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ), IsZero (G 0) ∧
        IsIsomorphic (G (Fin.last n)) X ∧ (∀ i, Mono (φ i)) ∧ ∀ i, P (cokernel (φ i)) := by
  constructor
  · intro hX
    induction hX with
    | @of_isZero X hX =>
      exact ⟨0, fun _ ↦ X, fun i ↦ i.elim0, hX, ⟨Iso.refl X⟩, fun i ↦ i.elim0,
        fun i ↦ i.elim0⟩
    | @of_mono X Y i _ hX hi ih =>
      obtain ⟨n, G, φ, h0, ⟨e⟩, hm, hP⟩ := ih
      let G' : Fin (n + 2) → C := fun j ↦ if h : (j : ℕ) < n + 1 then G ⟨j, h⟩ else Y
      have hG' (j : ℕ) (h : j < n + 1) : G' ⟨j, by omega⟩ = G ⟨j, h⟩ := dite_eq_left h
      have hG'last : G' (Fin.last (n + 1)) = Y := dite_eq_right (by simp)
      let φ' : ∀ j : Fin (n + 1), G' j.castSucc ⟶ G' j.succ := fun j ↦
        if h : (j : ℕ) < n then
          eqToHom (hG' j (by omega)) ≫ φ ⟨j, h⟩ ≫ eqToHom (hG' (j + 1) (by omega)).symm
        else
          eqToHom (hG' j (by omega)) ≫ eqToHom (congrArg G (Fin.ext (by simp; omega))) ≫ e.hom ≫ i ≫
            eqToHom ((congrArg G' (by ext; simp; omega)).trans hG'last).symm
      refine ⟨n + 1, G', φ', ?_, ⟨eqToIso hG'last⟩, fun j ↦ ?_, fun j ↦ ?_⟩
      · exact (hG' 0 (by omega)).symm ▸ h0
      · dsimp only [φ']
        split <;> infer_instance
      · dsimp only [φ']
        split
        · exact prop_cokernel_comp _ _ _ (hP _)
        · exact P.prop_of_iso (cokernelEpiComp _ _).symm
            (P.prop_of_iso (cokernelEpiComp _ _).symm
              (P.prop_of_iso (cokernelEpiComp _ _).symm
                (P.prop_of_iso (cokernelCompIsIso i _).symm hi)))
  · rintro ⟨n, G, φ, h0, ⟨e⟩, hm, hP⟩
    have key : ∀ (i : ℕ) (hi : i < n + 1), P.filtrationClosure (G ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero => exact fun _ ↦ .of_isZero h0
      | succ i ih =>
        intro hi
        have := hm ⟨i, by omega⟩
        exact .of_mono (φ ⟨i, _⟩) (ih _) (hP ⟨i, _⟩)
    exact P.filtrationClosure.prop_of_iso e (key n (by omega))

section FiveTerm

/-- Let `P` be closed under kernels, cokernels and extensions. If `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄ ⟶ X₅`
is exact at `X₂`, `X₃` and `X₄`, and `P` holds for `X₁`, `X₂`, `X₄` and `X₅`, then `P` holds
for `X₃`. -/
theorem prop_X₃_of_exact (P : ObjectProperty C)
    (hker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (kernel f))
    (hcoker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (cokernel f))
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {X₁ X₂ X₃ X₄ X₅ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄} {f₄ : X₄ ⟶ X₅}
    {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0}
    (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₃ : (ShortComplex.mk f₃ f₄ w₃).Exact)
    (hX₁ : P X₁) (hX₂ : P X₂) (hX₄ : P X₄) (hX₅ : P X₅) : P X₃ := by
  have : Mono (cokernel.desc f₁ f₂ w₁) := h₁.mono_cokernelDesc
  have : Epi (kernel.lift f₄ f₃ w₃) := h₃.epi_kernelLift
  have w : cokernel.desc f₁ f₂ w₁ ≫ kernel.lift f₄ f₃ w₃ = 0 := by
    ext
    simp [w₂]
  let S := ShortComplex.mk _ _ w
  let S' := ShortComplex.mk (cokernel.desc f₁ f₂ w₁) f₃ (by ext; simp [w₂])
  let φ : ShortComplex.mk f₂ f₃ w₂ ⟶ S' :=
    { τ₁ := cokernel.π f₁, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  let ψ : S ⟶ S' :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι f₄ }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h₂)
  exact hext S { exact := hS } (hcoker f₁ hX₁ hX₂) (hker f₄ hX₄ hX₅)

variable {D : Type*} [Category* D] [Abelian D]

/-- Variant of `CategoryTheory.ObjectProperty.prop_X₃_of_exact` in which the exact sequence
lives in an abelian category `D`, and its terms are identified with the images of objects of
`C` under a fully faithful exact functor `F : C ⥤ D`. -/
theorem prop_X₃_of_exact_of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : ObjectProperty C)
    (hker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (kernel f))
    (hcoker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (cokernel f))
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {Y₁ Y₂ Y₃ Y₄ Y₅ : D} {f₁ : Y₁ ⟶ Y₂} {f₂ : Y₂ ⟶ Y₃} {f₃ : Y₃ ⟶ Y₄} {f₄ : Y₄ ⟶ Y₅}
    {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0}
    (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₃ : (ShortComplex.mk f₃ f₄ w₃).Exact)
    {X₁ X₂ X₃ X₄ X₅ : C} (e₁ : Y₁ ≅ F.obj X₁) (e₂ : Y₂ ≅ F.obj X₂) (e₃ : Y₃ ≅ F.obj X₃)
    (e₄ : Y₄ ≅ F.obj X₄) (e₅ : Y₅ ≅ F.obj X₅)
    (hX₁ : P X₁) (hX₂ : P X₂) (hX₄ : P X₄) (hX₅ : P X₅) : P X₃ := by
  let g₁ := F.preimage (e₁.inv ≫ f₁ ≫ e₂.hom)
  let g₂ := F.preimage (e₂.inv ≫ f₂ ≫ e₃.hom)
  let g₃ := F.preimage (e₃.inv ≫ f₃ ≫ e₄.hom)
  let g₄ := F.preimage (e₄.inv ≫ f₄ ≫ e₅.hom)
  have v₁ : g₁ ≫ g₂ = 0 := F.map_injective (by simp [g₁, g₂, reassoc_of% w₁])
  have v₂ : g₂ ≫ g₃ = 0 := F.map_injective (by simp [g₂, g₃, reassoc_of% w₂])
  have v₃ : g₃ ≫ g₄ = 0 := F.map_injective (by simp [g₃, g₄, reassoc_of% w₃])
  have hex {Z₁ Z₂ Z₃ : C} {W₁ W₂ W₃ : D} (a : W₁ ⟶ W₂) (b : W₂ ⟶ W₃) (wab : a ≫ b = 0)
      (k₁ : W₁ ≅ F.obj Z₁) (k₂ : W₂ ≅ F.obj Z₂) (k₃ : W₃ ≅ F.obj Z₃)
      (hab : (ShortComplex.mk a b wab).Exact) (wg : F.preimage (k₁.inv ≫ a ≫ k₂.hom) ≫
        F.preimage (k₂.inv ≫ b ≫ k₃.hom) = 0) :
      (ShortComplex.mk _ _ wg).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ F]
    exact ShortComplex.exact_of_iso (ShortComplex.isoMk k₁ k₂ k₃ (by simp) (by simp)) hab
  exact prop_X₃_of_exact P hker hcoker hext (hex _ _ _ e₁ e₂ e₃ h₁ v₁)
    (hex _ _ _ e₂ e₃ e₄ h₂ v₂) (hex _ _ _ e₃ e₄ e₅ h₃ v₃) hX₁ hX₂ hX₄ hX₅


end FiveTerm

end CategoryTheory.ObjectProperty
