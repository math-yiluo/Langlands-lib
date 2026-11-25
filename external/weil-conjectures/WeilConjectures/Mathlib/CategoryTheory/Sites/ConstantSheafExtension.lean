/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Extensions of constant sheaves of modules are locally constant

Let `(C, J)` be a site and `0 ⟶ M_C ⟶ E ⟶ N_C ⟶ 0` a short exact sequence of sheaves of
modules over a noetherian ring `Λ` whose outer terms are constant, with `N` finitely generated.
Then `E` is locally constant: choose a presentation `0 ⟶ K ⟶ Λ^b ⟶ N ⟶ 0`; locally, the
generators of `N` lift to sections of `E`, which defines `Λ^b ⟶ E`; on `K` this lands in `M_C`
and is, after a further localisation, induced by a linear map `f : K ⟶ M`
(`CategoryTheory.exists_mem_forall_exists_linearMap_of_sections`). Then `E` is locally the
constant sheaf at the pushout of `M ← K ⟶ Λ^b`, by the five lemma
(`CategoryTheory.exists_mem_forall_isConstant_over_of_shortExact`).

This is the extension clause of blueprint `lemma-constructible-flc-serre`. The argument of the
blueprint (the sheaf of splittings is a torsor) only applies when the extension is locally
split, which fails for instance for `0 ⟶ ℤ/2 ⟶ ℤ/4 ⟶ ℤ/2 ⟶ 0` over `Λ = ℤ/4`; the presentation
argument above works for any noetherian `Λ`.
-/

@[expose] public section

universe v u v'

open CategoryTheory Limits Opposite

namespace CategoryTheory

section Sections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ : Type v'} [Ring Λ] [HasWeakSheafify J (ModuleCat.{v'} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)]

/-- **A linear map into the sections of a constant sheaf is locally constant**: for a finitely
generated module `K` and a linear map `L : K ⟶ N_C(T)`, there is a covering sieve of `T` over
whose members `U` not covered by the empty sieve, the restriction of `L` to `U` is the
composite of a linear map `K ⟶ N` with `N ⟶ N_C(U)`. -/
theorem exists_mem_forall_exists_linearMap_of_sections (K N : ModuleCat.{v'} Λ)
    [Module.Finite Λ K] {T : C}
    (L : K →ₗ[Λ] (CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj N)).obj (op T)) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (g : U ⟶ T), S g → (⊥ : Sieve U) ∉ J U → ∃ f : K →ₗ[Λ] N, ∀ k : K,
      (CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj N)).map g.op (L k) =
        (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op U) (f k) := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := K)
  obtain ⟨S, hS, h⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq N (U := T)
    (fun m : (t : Set K) ↦ L m.1)
  refine ⟨S, hS, fun U g hg hU ↦ ?_⟩
  choose n hn using h g hg
  have hinj := J.toSheafify_const_app_injective N hU
  let ιN := ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op U)).hom
  let L' := ((CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj N)).map g.op).hom ∘ₗ L
  have hle : LinearMap.range L' ≤ LinearMap.range ιN := by
    rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨n ⟨m, hm⟩, hn ⟨m, hm⟩⟩
  let e := LinearEquiv.ofInjective ιN hinj
  refine ⟨e.symm.toLinearMap ∘ₗ L'.codRestrict _ fun m ↦ hle (LinearMap.mem_range_self L' m),
    fun m ↦ ?_⟩
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨L' m, hle (LinearMap.mem_range_self L' m)⟩)
  rw [LinearEquiv.ofInjective_apply] at h
  exact h.symm

end Sections

end CategoryTheory

namespace CategoryTheory

namespace ExtensionOfConstant

variable {Λ : Type*} [Ring Λ] {M N : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup N]
  [Module Λ N] {b : ℕ} (p : (Fin b → Λ) →ₗ[Λ] N) (f : LinearMap.ker p →ₗ[Λ] M)

/-- The relations `(f k, -k)` defining the pushout of `M ← ker p ⟶ Λ^b`. -/
def relations : Submodule Λ (M × (Fin b → Λ)) :=
  LinearMap.range (f.prod (-(LinearMap.ker p).subtype))

/-- The pushout of `f : ker p ⟶ M` and the inclusion `ker p ⟶ Λ^b`: an extension of `N` by `M`
when `p` is surjective. -/
abbrev Pushout : Type _ := (M × (Fin b → Λ)) ⧸ relations p f

/-- The inclusion `M ⟶ Pushout p f`. -/
def inl : M →ₗ[Λ] Pushout p f := (relations p f).mkQ ∘ₗ LinearMap.inl Λ M (Fin b → Λ)

/-- The projection `Pushout p f ⟶ N` induced by `p`. -/
def proj : Pushout p f →ₗ[Λ] N :=
  (relations p f).liftQ (p ∘ₗ LinearMap.snd Λ M (Fin b → Λ)) (by
    rintro _ ⟨k, rfl⟩
    simp)

@[simp]
lemma proj_mk (m : M) (v : Fin b → Λ) :
    proj p f (Submodule.Quotient.mk (m, v)) = p v := rfl

@[simp]
lemma inl_apply (m : M) : inl p f m = Submodule.Quotient.mk (m, 0) := rfl

lemma proj_comp_inl : proj p f ∘ₗ inl p f = 0 := by
  ext m
  simp

lemma injective_inl : Function.Injective (inl p f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  rw [inl_apply, Submodule.Quotient.mk_eq_zero] at hm
  obtain ⟨k, hk⟩ := hm
  have h₂ := congrArg _root_.Prod.snd hk
  have h₁ := congrArg _root_.Prod.fst hk
  simp only [LinearMap.prod_apply, Function.prod, LinearMap.neg_apply, Submodule.subtype_apply,
    neg_eq_zero] at h₁ h₂
  have : k = 0 := Subtype.ext h₂
  rw [← h₁, this, map_zero]

lemma exact_inl_proj (y : Pushout p f) (hy : proj p f y = 0) : ∃ m, inl p f m = y := by
  obtain ⟨⟨m, v⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [proj_mk] at hy
  refine ⟨m + f ⟨v, hy⟩, ?_⟩
  rw [inl_apply, Submodule.Quotient.eq]
  refine ⟨⟨v, hy⟩, ?_⟩
  simp

lemma surjective_proj (hp : Function.Surjective p) : Function.Surjective (proj p f) := by
  intro n
  obtain ⟨v, rfl⟩ := hp n
  exact ⟨Submodule.Quotient.mk (0, v), rfl⟩

end ExtensionOfConstant

section Extension

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ : Type v'} [Ring Λ] [HasSheafify J (ModuleCat.{v'} Λ)]
  (V : C) [HasSheafify (J.over V) (ModuleCat.{v'} Λ)]
  [PreservesFiniteLimits (J.overPullback (ModuleCat.{v'} Λ) V)]
  [PreservesFiniteColimits (J.overPullback (ModuleCat.{v'} Λ) V)]

open ExtensionOfConstant in
/-- **An extension of constant sheaves is constant once a presentation lifts.** Let
`0 ⟶ M_C ⟶ E ⟶ N_C ⟶ 0` be short exact (through `e₁`, `e₃`), let `p : Λ^b ⟶ N` be surjective
and suppose that over `V` the generators `p(eᵢ)` lift to sections `xᵢ` of `E`, and that on
`ker p` the induced map `Λ^b ⟶ E(V)` is given by a linear map `f : ker p ⟶ M`. Then the
restriction of `E` to `V` is the constant sheaf at the pushout of `M ← ker p ⟶ Λ^b`. -/
theorem Sheaf.isConstant_over_of_shortExact_of_sections {M N : ModuleCat.{v'} Λ}
    [IsIso (constantSheafOverHom J (ModuleCat.{v'} Λ) V M)]
    [IsIso (constantSheafOverHom J (ModuleCat.{v'} Λ) V N)]
    {S : ShortComplex (Sheaf J (ModuleCat.{v'} Λ))} (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ (constantSheaf J _).obj M) (e₃ : S.X₃ ≅ (constantSheaf J _).obj N)
    {b : ℕ} (p : (Fin b → Λ) →ₗ[Λ] N) (hp : Function.Surjective p)
    (x : Fin b → S.X₂.obj.obj (op V))
    (hx : ∀ i, S.g.hom.app (op V) (x i) = e₃.inv.hom.app (op V)
      ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op V)
        (p (Pi.single i 1))))
    (f : LinearMap.ker p →ₗ[Λ] M)
    (hf : ∀ k : LinearMap.ker p, S.f.hom.app (op V) (e₁.inv.hom.app (op V)
      ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V) (f k))) =
        Fintype.linearCombination Λ x k) :
    (S.X₂.over V).IsConstant (J.over V) := by
  classical
  let κM := (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V)
  let κN := (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op V)
  let lP : Pushout p f →ₗ[Λ] S.X₂.obj.obj (op V) :=
    (relations p f).liftQ ((S.f.hom.app (op V)).hom ∘ₗ (e₁.inv.hom.app (op V)).hom ∘ₗ κM.hom ∘ₗ
      LinearMap.fst Λ M (Fin b → Λ) + Fintype.linearCombination Λ x ∘ₗ
        LinearMap.snd Λ M (Fin b → Λ)) (by
      rintro _ ⟨k, rfl⟩
      rw [LinearMap.mem_ker]
      change S.f.hom.app (op V) (e₁.inv.hom.app (op V) (κM (f k))) +
        Fintype.linearCombination Λ x (-(k : Fin b → Λ)) = 0
      rw [map_neg, hf k]
      exact add_neg_cancel _)
  let adj := constantSheafAdj (J.over V) (ModuleCat.{v'} Λ) Over.mkIdTerminal
  let τ₂ : (constantSheaf (J.over V) _).obj (ModuleCat.of Λ (Pushout p f)) ⟶ S.X₂.over V :=
    (adj.homEquiv _ _).symm (ModuleCat.ofHom lP)
  let SP : ShortComplex (ModuleCat.{v'} Λ) :=
    ShortComplex.mk (X₁ := M) (X₂ := ModuleCat.of Λ (Pushout p f)) (X₃ := N)
      (ModuleCat.ofHom (inl p f)) (ModuleCat.ofHom (proj p f))
      (ModuleCat.hom_ext (proj_comp_inl p f))
  have hSP : SP.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff _).2 fun y hy ↦ exact_inl_proj p f y hy
      mono_f := (ModuleCat.mono_iff_injective _).2 (injective_inl p f)
      epi_g := (ModuleCat.epi_iff_surjective _).2 (surjective_proj p f hp) }
  have hz (y : S.X₁.obj.obj (op V)) : S.g.hom.app (op V) (S.f.hom.app (op V) y) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
    rfl
  let Φ : SP.map (constantSheaf (J.over V) _) ⟶ S.map (J.overPullback _ V) :=
    { τ₁ := constantSheafOverHom J _ V M ≫ (J.overPullback _ V).map e₁.inv
      τ₂ := τ₂
      τ₃ := constantSheafOverHom J _ V N ≫ (J.overPullback _ V).map e₃.inv
      comm₁₂ := by
        change (constantSheafOverHom J _ V M ≫ (J.overPullback _ V).map e₁.inv) ≫
            (J.overPullback _ V).map S.f =
          (constantSheaf (J.over V) _).map (ModuleCat.ofHom (inl p f)) ≫ τ₂
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, adj.homEquiv_naturality_right,
          adj.homEquiv_naturality_right, constantSheafAdj_homEquiv_constantSheafOverHom]
        ext m
        change _ = lP (Submodule.Quotient.mk (m, 0))
        simp [lP, κM]
        rfl
      comm₂₃ := by
        change τ₂ ≫ (J.overPullback _ V).map S.g =
          (constantSheaf (J.over V) _).map (ModuleCat.ofHom (proj p f)) ≫
            constantSheafOverHom J _ V N ≫ (J.overPullback _ V).map e₃.inv
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
          adj.homEquiv_naturality_right, constantSheafAdj_homEquiv_constantSheafOverHom]
        refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.prod_ext ?_ ?_))
        · ext m
          change S.g.hom.app (op V) (lP (Submodule.Quotient.mk (m, 0))) =
            e₃.inv.hom.app (op V) (κN (p 0))
          simp [lP, hz]
        · refine LinearMap.pi_ext fun i r ↦ ?_
          change S.g.hom.app (op V) (lP (Submodule.Quotient.mk (0, Pi.single i r))) =
            e₃.inv.hom.app (op V) (κN (p (Pi.single i r)))
          have hr : (Pi.single i r : Fin b → Λ) = r • Pi.single i 1 := by
            rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [hr, map_smul, map_smul, map_smul]
          simp [lP, hx]
          rfl }
  have := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ Φ (hSP.map_of_exact _) (hS.map_of_exact _)
  exact Sheaf.isConstant_of_iso _ (asIso Φ.τ₂).symm

end Extension

end CategoryTheory
