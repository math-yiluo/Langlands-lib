/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechH1MapNatural
import WeilConjectures.AlgebraicGeometry.ModuleCechResolutionColumnZero
import Mathlib.Algebra.Homology.Refinements

/-! # Injectivity of the first Čech cohomology map

Source: Stacks Project, Cohomology, Lemma 0B8R (blueprint: lem-sc-cech-h1-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def totalProjection {C : Type*} [Category C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q n : ℕ) : (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X p).X q := by
  classical
  exact K.totalDesc fun p' q' _ ↦
    if hp : p' = p then
      if hq : q' = q then (K.XXIsoOfEq _ _ _ hp hq).hom else 0
    else 0

private theorem total_zero_decomposition {C : Type*} [Category C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    totalProjection K 0 0 0 ≫ K.ιTotal (ComplexShape.up ℕ) 0 0 0 (by simp) = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  have hp : p = 0 := by change p + q = 0 at h; omega
  have hq : q = 0 := by change p + q = 0 at h; omega
  subst p q
  simp [totalProjection]

private theorem total_zero_d {C : Type*} [Category C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K.ιTotal (ComplexShape.up ℕ) 0 0 0 (by simp) ≫
        (K.total (ComplexShape.up ℕ)).d 0 1 =
      (K.d 0 1).f 0 ≫ K.ιTotal (ComplexShape.up ℕ) 1 0 1 (by simp) +
        (K.X 0).d 0 1 ≫ K.ιTotal (ComplexShape.up ℕ) 0 1 1 (by simp) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq' _ _ (by simp : (ComplexShape.up ℕ).Rel 0 1),
    HomologicalComplex₂.d₂_eq' _ _ 0 (by simp : (ComplexShape.up ℕ).Rel 0 1)]
  rw [K.ιTotalOrZero_eq (ComplexShape.up ℕ) 1 0 1 (by simp),
    K.ιTotalOrZero_eq (ComplexShape.up ℕ) 0 1 1 (by simp)]
  simp

/-- A boundary in total degree one lifts to a boundary of the augmented complex:
the (1,0) component forces the total degree-zero primitive into the augmentation
kernel, and the (0,1) component then identifies the original boundary. -/
private theorem mono_homology_one_of_column_kernels {C : Type*} [Category C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (A : CochainComplex C ℕ) (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (b : A ⟶ K.total (ComplexShape.up ℕ))
    (hb : ∀ n : ℕ, b.f n = a.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (hker : ∀ n : ℕ, Nonempty (IsLimit (KernelFork.ofι (a.f n)
      (by simpa using congrArg (fun f ↦ f.f n) ha)))) :
    Mono (HomologicalComplex.homologyMap b 1) := by
  classical
  apply (HomologicalComplex.mono_homologyMap_iff_up_to_refinements b
    0 1 2 (by simp) (by simp)).2
  intro W z _ t ht
  let t₀ := t ≫ totalProjection K 0 0 0
  have ht₀ : t = t₀ ≫ K.ιTotal (ComplexShape.up ℕ) 0 0 0 (by simp) := by
    simp [t₀, total_zero_decomposition]
  have hd : z ≫ a.f 1 ≫ K.ιTotal (ComplexShape.up ℕ) 0 1 1 (by simp) =
      t₀ ≫ ((K.d 0 1).f 0 ≫ K.ιTotal (ComplexShape.up ℕ) 1 0 1 (by simp) +
        (K.X 0).d 0 1 ≫ K.ιTotal (ComplexShape.up ℕ) 0 1 1 (by simp)) := by
    rw [← hb, ht, ht₀, Category.assoc, total_zero_d]
  have hv : t₀ ≫ (K.d 0 1).f 0 = 0 := by
    have h := congrArg (fun f ↦ f ≫ totalProjection K 1 0 1) hd
    simpa [totalProjection, Preadditive.add_comp, Preadditive.comp_add] using h.symm
  let l := (hker 0).some
  let x := l.lift (KernelFork.ofι t₀ hv)
  have hx : x ≫ a.f 0 = t₀ := l.fac _ WalkingParallelPair.zero
  have hh : z ≫ a.f 1 = t₀ ≫ (K.X 0).d 0 1 := by
    have h := congrArg (fun f ↦ f ≫ totalProjection K 0 1 1) hd
    simpa [totalProjection, Preadditive.add_comp, Preadditive.comp_add] using h
  have : Mono (a.f 1) := Fork.IsLimit.mono (hker 1).some
  refine ⟨W, 𝟙 W, inferInstance, x, ?_⟩
  rw [Category.id_comp]
  apply (cancel_mono (a.f 1)).1
  rw [Category.assoc, ← a.comm, ← Category.assoc, hx, hh]

/-- The canonical map from first Čech cohomology of an open cover to first module
cohomology is injective. Source: Stacks Project, Cohomology, Lemma 0B8R
(blueprint: lem-sc-cech-h1-injective).

Proof: take the canonical comparison supplied by `cechH1Map_natural` (Stacks 01EQ).
For an injective resolution I, the augmentation of Cech cochains into each resolution
column is its degree-zero kernel, by `moduleCech_resolution_column_zero`. If the image
of a degree-one cycle is a total boundary, its primitive lies in the sole degree-zero
summand (0,0). Projection of its differential to (1,0) is zero, so the kernel property
lifts this primitive to a degree-zero Cech cochain. Projection to (0,1), followed by
cancellation of the monomorphic column augmentation, identifies its Cech differential
with the original cycle. Thus H¹(beta) is monomorphic. The defining comparison equation
factors H¹(beta) through c, so c is monomorphic and therefore injective. This is an
elementary low-degree chase in the double complex of Tag 01EQ, written by G1. -/
theorem cechH1_injective (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) :
    ∃ c : ∀ F : X.Modules,
        ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology 1 ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace 1).obj F,
      (∀ F : X.Modules, IsModuleCechComparison U F 1 (c F)) ∧
      (∀ F : X.Modules, Function.Injective (c F).hom) := by
  classical
  obtain ⟨c, hc, _⟩ := cechH1Map_natural X U hcover
  refine ⟨c, hc, ?_⟩
  intro F
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let I := injectiveResolution F
  let A := (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat
  let K := moduleCechDouble U I
  let a : A ⟶ K.X 0 :=
    (CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (I.ι.f 0).val)
  have ha : a ≫ K.d 0 1 = 0 := by
    let (J : Type u) :
        HasLimitsOfShape (Discrete J) (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) :=
      ModuleCat.hasLimitsOfShape
    let G := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
    rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]
  have hker : ∀ n : ℕ, Nonempty (IsLimit (KernelFork.ofι (a.f n)
      (by simpa using congrArg (fun f ↦ f.f n) ha))) := by
    intro n
    have h := moduleCech_resolution_column_zero U F I ha n
    rw [CochainComplex.quasiIsoAt₀_iff] at h
    rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp) (by simp)] at h
    rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel] at h
    simpa only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using h
  have hmono : Mono (HomologicalComplex.homologyMap (moduleCechBeta U I) 1) :=
    mono_homology_one_of_column_kernels K A a ha (moduleCechBeta U I)
      (fun _ ↦ rfl) hker
  have hcomp := hc F I
  have : Mono (c F) := mono_of_mono_fac hcomp
  exact (ModuleCat.mono_iff_injective (c F)).1 inferInstance

end AlgebraicGeometry.Scheme.Modules
