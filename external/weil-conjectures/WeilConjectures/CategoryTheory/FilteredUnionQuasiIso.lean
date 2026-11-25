/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Basic

public import WeilConjectures.CategoryTheory.FiniteFiltrationInduction

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequenceLemmas
/-!
# Quasi-isomorphisms from a filtered resolution union

Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, union and part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A basic filtered complex is degreewise free, with free filtered steps and free graded
pieces, and with zero differential.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, definition of a basic filtered complex
(blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
def IsBasicFilteredComplex {R : Type u} [CommRing R]
    (B : WeilFilteredObject
      (CochainComplex (ModuleCat.{v} R) ℤ)) : Prop :=
  (∀ n : ℤ, Module.Free R (B.obj.X n)) ∧
    (∀ i n : ℤ, Module.Free R
      ((B.filtration.step i : CochainComplex (ModuleCat.{v} R) ℤ).X n)) ∧
    (∀ i n : ℤ, Module.Free R ((B.filtration.gradedPiece i).X n)) ∧
    (∀ n : ℤ, B.obj.d n (n + 1) = 0)

private theorem cycle_element {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (x : L.X n)
    (hx : L.d n (n + 1) x = 0) :
    ∃ z : L.cycles n, L.iCycles n z = x := by
  have hx' : (L.sc n).g x = 0 := by
    change L.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
    exact hx
  let z := (L.sc n).moduleCatCyclesIso.inv ⟨x, hx'⟩
  refine ⟨z, ?_⟩
  exact ConcreteCategory.congr_hom (L.sc n).moduleCatCyclesIso_inv_iCycles ⟨x, hx'⟩

private theorem union_quasiIso {R : Type u} [CommRing R]
    (P : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (inc : ∀ m, P m ⟶ P (m + 1))
    (K U : CochainComplex (ModuleCat.{v} R) ℤ)
    (f : ∀ m, P m ⟶ K) (j : ∀ m, P m ⟶ U) (fU : U ⟶ K)
    (hj : ∀ m, Mono (j m))
    (hincU : ∀ m, inc m ≫ j (m + 1) = j m)
    (hf : ∀ m, j m ≫ fU = f m)
    (hunion : ∀ (n : ℤ) (x : U.X n), ∃ (m : ℕ) (y : (P m).X n), (j m).f n y = x)
    (hzero : ∀ n, Epi (HomologicalComplex.homologyMap (f 0) n))
    (hkill : ∀ m n, kernel.ι (HomologicalComplex.homologyMap (f m) n) ≫
      HomologicalComplex.homologyMap (inc m) n = 0) : QuasiIso fU := by
  classical
  have hrep (n : ℤ) (x : U.homology n) :
      ∃ (m : ℕ) (y : (P m).homology n), HomologicalComplex.homologyMap (j m) n y = x := by
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (U.homologyπ n)).mp inferInstance x
    obtain ⟨m, y, hy⟩ := hunion n (U.iCycles n z)
    have : Mono (j m) := hj m
    have hycycle : (P m).d n (n + 1) y = 0 := by
      apply (ModuleCat.mono_iff_injective ((j m).f (n + 1))).mp inferInstance
      have hw := ConcreteCategory.congr_hom ((j m).comm n (n + 1)) y
      have hz := ConcreteCategory.congr_hom (U.iCycles_d n (n + 1)) z
      simp only [ModuleCat.comp_apply] at hw hz
      rw [hy] at hw
      simpa only [map_zero, ModuleCat.hom_zero, LinearMap.zero_apply] using hw.symm.trans hz
    obtain ⟨c, hc⟩ := cycle_element (P m) n y hycycle
    have hcmap : HomologicalComplex.cyclesMap (j m) n c = z := by
      apply (ModuleCat.mono_iff_injective (U.iCycles n)).mp inferInstance
      have hw := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (j m) n) c
      simpa only [ModuleCat.comp_apply, hc, hy] using hw
    refine ⟨m, (P m).homologyπ n c, ?_⟩
    have hw := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (j m) n) c
    simpa only [ModuleCat.comp_apply, hcmap] using hw
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
  constructor
  · rw [ModuleCat.mono_iff_injective]
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨m, y, hy⟩ := hrep n x
    have hfmap := congrArg (fun a ↦ HomologicalComplex.homologyMap a n) (hf m)
    rw [HomologicalComplex.homologyMap_comp] at hfmap
    have hyzero : HomologicalComplex.homologyMap (f m) n y = 0 := by
      rw [← hfmap, ModuleCat.comp_apply, hy, hx]
    let c := (ModuleCat.kernelIsoKer (HomologicalComplex.homologyMap (f m) n)).inv
      ⟨y, hyzero⟩
    have hc : kernel.ι (HomologicalComplex.homologyMap (f m) n) c = y :=
      ConcreteCategory.congr_hom
        (ModuleCat.kernelIsoKer_inv_kernel_ι (HomologicalComplex.homologyMap (f m) n))
        ⟨y, hyzero⟩
    have hykill : HomologicalComplex.homologyMap (inc m) n y = 0 := by
      have hw := ConcreteCategory.congr_hom (hkill m n) c
      simpa only [ModuleCat.comp_apply, hc, ModuleCat.hom_zero, LinearMap.zero_apply] using hw
    have hjmap := congrArg (fun a ↦ HomologicalComplex.homologyMap a n) (hincU m)
    rw [HomologicalComplex.homologyMap_comp] at hjmap
    rw [← hy, ← hjmap, ModuleCat.comp_apply, hykill, map_zero]
  · have : Epi (HomologicalComplex.homologyMap (f 0) n) := hzero n
    exact epi_of_epi_fac
      (f := HomologicalComplex.homologyMap (j 0) n)
      (h := HomologicalComplex.homologyMap (f 0) n) (by
        simpa only [← HomologicalComplex.homologyMap_comp] using
          congrArg (fun a ↦ HomologicalComplex.homologyMap a n) (hf 0))

/-- The restriction of a filtered morphism to the `p`-th step commutes with the step arrows.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
theorem WeilFilteredObject.restriction_arrow {C : Type*} [Category* C] [Abelian C]
    {A B : WeilFilteredObject C} (φ : A ⟶ B) (p : ℤ) :
    WeilFilteredObject.restriction φ p ≫ (B.filtration.F p).arrow =
      (A.filtration.F p).arrow ≫ φ.hom :=
  Classical.choose_spec (φ.preserves p)

/-- The filtration-step restriction of a composite filtered morphism is the composite of the
restrictions, since the step arrows are monomorphisms.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
theorem WeilFilteredObject.restriction_comp {C : Type*} [Category* C] [Abelian C]
    {A B D : WeilFilteredObject C} (φ : A ⟶ B) (ψ : B ⟶ D) (p : ℤ) :
    WeilFilteredObject.restriction (φ ≫ ψ) p =
      WeilFilteredObject.restriction φ p ≫ WeilFilteredObject.restriction ψ p := by
  rw [← cancel_mono (D.filtration.F p).arrow, WeilFilteredObject.restriction_arrow, Category.assoc,
    WeilFilteredObject.restriction_arrow, ← Category.assoc, WeilFilteredObject.restriction_arrow,
    Category.assoc]
  rfl

/-- The short exact sequence `0 → F^{p+1} → F^p → gr^p → 0` of a filtered object.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
noncomputable def WeilFilteredObject.grShortComplex {C : Type*} [Category* C] [Abelian C]
    (A : WeilFilteredObject C) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (Subobject.ofLE (A.filtration.F (p + 1)) (A.filtration.F p)
    (A.filtration.F_succ_le p)) (cokernel.π _) (cokernel.condition _)

/-- The sequence `0 → F^{p+1} → F^p → gr^p → 0` is short exact.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
theorem WeilFilteredObject.grShortComplex_shortExact {C : Type*} [Category* C] [Abelian C]
    (A : WeilFilteredObject C) (p : ℤ) : (A.grShortComplex p).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (inferInstanceAs (Mono (Subobject.ofLE _ _ _)))
    (by
      dsimp [WeilFilteredObject.grShortComplex]
      infer_instance)

/-- Step restriction of filtered morphisms commutes with the inclusions of steps.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
theorem WeilFilteredObject.ofLE_comp_restriction {C : Type*} [Category* C] [Abelian C]
    {A B : WeilFilteredObject C} (φ : A ⟶ B) (p : ℤ) :
    Subobject.ofLE (A.filtration.F (p + 1)) (A.filtration.F p) (A.filtration.F_succ_le p) ≫
        WeilFilteredObject.restriction φ p =
      WeilFilteredObject.restriction φ (p + 1) ≫
        Subobject.ofLE (B.filtration.F (p + 1)) (B.filtration.F p)
          (B.filtration.F_succ_le p) := by
  rw [← cancel_mono (B.filtration.F p).arrow, Category.assoc, Category.assoc,
    Subobject.ofLE_arrow, WeilFilteredObject.restriction_arrow, ← Category.assoc,
    Subobject.ofLE_arrow, WeilFilteredObject.restriction_arrow]

/-- A map of graded pieces compatible with a filtered morphism gives a morphism of the short
exact sequences `0 → F^{p+1} → F^p → gr^p → 0`.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
noncomputable def WeilFilteredObject.grShortComplexMap {C : Type*} [Category* C] [Abelian C]
    {A B : WeilFilteredObject C} (φ : A ⟶ B) (p : ℤ) (g : A.filtration.gr p ⟶ B.filtration.gr p)
    (hg : cokernel.π _ ≫ g = WeilFilteredObject.restriction φ p ≫ cokernel.π _) :
    A.grShortComplex p ⟶ B.grShortComplex p where
  τ₁ := WeilFilteredObject.restriction φ (p + 1)
  τ₂ := WeilFilteredObject.restriction φ p
  τ₃ := g
  comm₁₂ := (WeilFilteredObject.ofLE_comp_restriction φ p).symm
  comm₂₃ := hg.symm

/-- The union of an increasing chain of filtered complexes `P₀ ⊂ P₁ ⊂ ⋯` mapping
compatibly to a filtered complex `K` maps quasi-isomorphically to `K`, on the total complex,
on every filtration step and on every graded piece, provided `f₀` is surjective on cohomology
(totally and on each step) and each inclusion kills the kernel of `H(f_m)` (totally and on
each step).
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, union and part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
theorem filteredUnion_quasiIso {R : Type u} [CommRing R]
    (P : ℕ → WeilFilteredObject (CochainComplex (ModuleCat.{v} R) ℤ))
    (inc : ∀ m, P m ⟶ P (m + 1))
    (K U : WeilFilteredObject (CochainComplex (ModuleCat.{v} R) ℤ))
    (f : ∀ m, P m ⟶ K) (j : ∀ m, P m ⟶ U) (fU : U ⟶ K)
    (hj : ∀ m, Mono (j m).hom)
    (hincU : ∀ m, inc m ≫ j (m + 1) = j m)
    (hf : ∀ m, j m ≫ fU = f m)
    (hunion : ∀ (n : ℤ) (x : U.obj.X n), ∃ (m : ℕ) (y : (P m).obj.X n), (j m).hom.f n y = x)
    (hunionStep : ∀ (p n : ℤ)
      (x : (U.filtration.F p : CochainComplex (ModuleCat.{v} R) ℤ).X n),
      ∃ (m : ℕ) (y : ((P m).filtration.F p : CochainComplex (ModuleCat.{v} R) ℤ).X n),
        (WeilFilteredObject.restriction (j m) p).f n y = x)
    (hzero : ∀ n, Epi (HomologicalComplex.homologyMap (f 0).hom n))
    (hzeroStep : ∀ p n,
      Epi (HomologicalComplex.homologyMap (WeilFilteredObject.restriction (f 0) p) n))
    (hkill : ∀ m n, kernel.ι (HomologicalComplex.homologyMap (f m).hom n) ≫
      HomologicalComplex.homologyMap (inc m).hom n = 0)
    (hkillStep : ∀ m p n,
      kernel.ι (HomologicalComplex.homologyMap (WeilFilteredObject.restriction (f m) p) n) ≫
        HomologicalComplex.homologyMap (WeilFilteredObject.restriction (inc m) p) n = 0) :
    QuasiIso fU.hom ∧ (∀ p, QuasiIso (WeilFilteredObject.restriction fU p)) ∧
      ∀ (p : ℤ) (g : U.filtration.gr p ⟶ K.filtration.gr p),
        cokernel.π _ ≫ g = WeilFilteredObject.restriction fU p ≫ cokernel.π _ → QuasiIso g := by
  have hstep (p : ℤ) : QuasiIso (WeilFilteredObject.restriction fU p) := by
    refine union_quasiIso
      (fun m ↦ ((P m).filtration.F p : CochainComplex (ModuleCat.{v} R) ℤ))
      (fun m ↦ WeilFilteredObject.restriction (inc m) p) _ _
      (fun m ↦ WeilFilteredObject.restriction (f m) p)
      (fun m ↦ WeilFilteredObject.restriction (j m) p)
      _ (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (hunionStep p) (hzeroStep p)
      (fun m ↦ hkillStep m p)
    · have := hj m
      have : Mono (WeilFilteredObject.restriction (j m) p ≫ (U.filtration.F p).arrow) := by
        rw [WeilFilteredObject.restriction_arrow]
        infer_instance
      exact mono_of_mono _ (U.filtration.F p).arrow
    · rw [← WeilFilteredObject.restriction_comp, hincU]
    · rw [← WeilFilteredObject.restriction_comp, hf]
  refine ⟨union_quasiIso (fun m ↦ (P m).obj) (fun m ↦ (inc m).hom) K.obj U.obj
    (fun m ↦ (f m).hom) (fun m ↦ (j m).hom) fU.hom hj (fun m ↦ congrArg (·.hom) (hincU m))
    (fun m ↦ congrArg (·.hom) (hf m)) hunion hzero hkill, hstep, fun p g hg ↦ ?_⟩
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (WeilFilteredObject.grShortComplexMap fU p g hg) (U.grShortComplex_shortExact p)
    (K.grShortComplex_shortExact p) (hstep (p + 1)) (hstep p)

end CategoryTheory
