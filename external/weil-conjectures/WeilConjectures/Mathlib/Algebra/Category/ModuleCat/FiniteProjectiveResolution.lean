/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Projective resolutions by finitely generated modules

Over a noetherian ring `R`, every finitely generated `R`-module `M` admits a projective
resolution all of whose terms are finitely generated
(`ModuleCat.exists_projectiveResolution_moduleFinite`).

The construction mimics `CategoryTheory.ProjectiveResolution.of`, but uses a custom choice of
projective presentation: a finitely generated module is presented by a finite free module
`Fin n → R`. Since kernels of maps out of finitely generated modules over a noetherian ring are
finitely generated, every term of the resulting resolution is finitely generated.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace ModuleCat.FiniteProjectiveResolution

variable {R : Type u} [CommRing R]

open Classical in
/-- A projective presentation of an `R`-module, which is a finite free module whenever the
module is finitely generated. -/
def pres (Z : ModuleCat.{u} R) : ProjectivePresentation Z :=
  if h : Module.Finite R Z then
    have hf := (Module.Finite.exists_fin' R Z).choose_spec.choose_spec
    { p := ModuleCat.of R (Fin (Module.Finite.exists_fin' R Z).choose → R)
      projective := ModuleCat.projective_of_free (Pi.basisFun R _)
      f := ModuleCat.ofHom (Module.Finite.exists_fin' R Z).choose_spec.choose
      epi := by
        rw [ModuleCat.epi_iff_surjective]
        exact hf }
  else (EnoughProjectives.presentation Z).some

/-- The projective object of `pres Z` is finitely generated if `Z` is. -/
lemma pres_finite (Z : ModuleCat.{u} R) [h : Module.Finite R Z] :
    Module.Finite R (pres Z).p := by
  rw [pres, dite_eq_left h]
  dsimp
  infer_instance

/-- The kernel of a morphism out of a finitely generated module over a noetherian ring is
finitely generated. -/
lemma kernel_finite [IsNoetherianRing R] {X Y : ModuleCat.{u} R} [Module.Finite R X]
    (f : X ⟶ Y) : Module.Finite R (kernel f : ModuleCat.{u} R) :=
  Module.Finite.equiv (ModuleCat.kernelIsoKer f).symm.toLinearEquiv

/-- The object mapping onto the kernel of `f` via the chosen presentation `pres`. -/
abbrev syz {X Y : ModuleCat.{u} R} (f : X ⟶ Y) : ModuleCat.{u} R := (pres (kernel f)).p

/-- The composition `syz f ⟶ kernel f ⟶ X`. -/
abbrev d {X Y : ModuleCat.{u} R} (f : X ⟶ Y) : syz f ⟶ X := (pres (kernel f)).f ≫ kernel.ι f

/-- The object `syz f` is finitely generated if the source of `f` is. -/
lemma syz_finite [IsNoetherianRing R] {X Y : ModuleCat.{u} R} [Module.Finite R X]
    (f : X ⟶ Y) : Module.Finite R (syz f) := by
  have := kernel_finite f
  exact pres_finite _

/-- `d f` and `f` are exact. -/
theorem exact_d_f {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    (ShortComplex.mk (d f) f (by simp)).Exact := by
  let α : ShortComplex.mk (d f) f (by simp) ⟶ ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := (pres (kernel f)).f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

variable (Z : ModuleCat.{u} R)

/-- The underlying chain complex of the projective resolution. -/
def ofComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.mk' (pres Z).p (syz (pres Z).f) (d (pres Z).f) (fun f => ⟨_, d f, by simp⟩)

/-- The differential `1 ⟶ 0` of `ofComplex Z`. -/
lemma ofComplex_d_1_0 : (ofComplex Z).d 1 0 = d (pres Z).f := by
  simp [ofComplex]

/-- `ofComplex Z` is exact in positive degrees. -/
lemma ofComplex_exactAt_succ (n : ℕ) : (ofComplex Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  match n with
  | 0 => apply exact_d_f
  | n + 1 => apply exact_d_f

/-- The terms of `ofComplex Z` are projective. -/
instance (n : ℕ) : Projective ((ofComplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply ProjectivePresentation.projective

set_option backward.defeqAttrib.useBackward true in
/-- A projective resolution of `Z` built from the presentations `pres`. -/
def of : ProjectiveResolution Z where
  complex := ofComplex Z
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨(pres Z).f, by
          rw [ofComplex_d_1_0, Category.assoc, kernel.condition, Limits.comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_d_f (pres Z).f, by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [ofComplex]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply ofComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- The terms of `ofComplex Z` are finitely generated if `Z` is. -/
lemma ofComplex_finite [IsNoetherianRing R] [Module.Finite R Z] :
    ∀ n, Module.Finite R ((ofComplex Z).X n)
  | 0 => pres_finite Z
  | 1 => by
    have := pres_finite Z
    exact syz_finite _
  | n + 2 => by
    have := ofComplex_finite n.succ
    have := syz_finite ((ofComplex Z).d (n + 1) n)
    let e : (ofComplex Z).X (n + 2) ≅ syz ((ofComplex Z).d (n + 1) n) :=
      ChainComplex.mk'XIso _ _ _ _ n
    exact Module.Finite.equiv e.symm.toLinearEquiv

end ModuleCat.FiniteProjectiveResolution

/-- Over a noetherian ring, a finitely generated module has a projective resolution whose terms
are finitely generated. -/
theorem ModuleCat.exists_projectiveResolution_moduleFinite {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : CategoryTheory.ProjectiveResolution M, ∀ n, Module.Finite R (P.complex.X n) :=
  ⟨FiniteProjectiveResolution.of M, fun n => FiniteProjectiveResolution.ofComplex_finite M n⟩
