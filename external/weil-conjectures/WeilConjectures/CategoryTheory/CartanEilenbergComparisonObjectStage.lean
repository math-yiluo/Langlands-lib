/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.CartanEilenbergComparisonObjectStage.Rows
import WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource

/-! # The object stage of a Cartan–Eilenberg comparison

Source: Stacks Project, Tags 015I and 015K, with the lifting property of Tag 013P(2).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem cycleObjectRow_shortExact
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ)) (p : ℤ) :
    (cartanEilenbergCycleObjectRow I p).ShortExact where
  exact := (cartanEilenbergCycleObjectRow I p).exact_of_f_is_kernel
    (isKernelOfComp (image.ι (I.d p (p + 1))) (I.d p (p + 1))
      (I.cyclesIsKernel p (p + 1) (by simp)) (cartanEilenbergCycleObjectRow I p).zero
      (image.fac (I.d p (p + 1))))
  mono_f := by change Mono (I.iCycles p); infer_instance
  epi_g := by change Epi (factorThruImage (I.d p (p + 1))); infer_instance

/-- Extend a specified augmented cycle map through the object column.
No incoming boundary map or homology comparison is involved.

Source: Stacks Project, Tags 015I, 015K and 013P(2);
(blueprint: lem-weil-pbc-ce-comparison-object-stage).

Proof: Use q-1=p to form the short exact sequence cycles → object → outgoing boundary
of resolution complexes, and the analogous sequence for J. Evaluation is exact and F
preserves short exact sequences. Identify the corresponding single-bicomplex columns
with the single complexes on Z^p(K), K^p and B^q(K), naturally with respect to u.
The assumed equation for y, after cancelling the monomorphic target cycle inclusion,
is precisely the augmented cycle square. Lift the outgoing boundary augmentation into
the termwise injective outgoing boundary column of J along the source boundary
augmentation by Tag 013P(2); nonnegative indexing and its quasi-isomorphism imply that
this augmentation is monomorphic. Call the resulting outgoing map c. Its augmentation agrees with
the boundary map induced by u.
Apply the exact-source horseshoe morphism
theorem to the cycles/object/outgoing-boundary sequence, with prescribed endpoints
y and c. Its middle map x gives the object augmentation and the displayed cycle square.
Thus only this second short exact sequence is used; the cycle map is an input. -/
theorem exists_cartanEilenberg_comparison_object_stage
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (p q : ℤ) (hq : q = p + 1)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIcol : QuasiIso (eI.f p))
    (hIcycles : QuasiIso (HomologicalComplex.cyclesMap eI p))
    (hIout : QuasiIso
      (image.map (Arrow.homMk' (eI.f (q - 1)) (eI.f q) (eI.comm (q - 1) q))))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJcol : QuasiIso (eJ.f p))
    (hJinj : ∀ n : ℕ, Injective ((J.X p).X n))
    (hJcyclesInj : ∀ n : ℕ, Injective ((J.cycles p).X n))
    (hJcycles : QuasiIso (HomologicalComplex.cyclesMap eJ p))
    (hJout : QuasiIso
      (image.map (Arrow.homMk' (eJ.f (q - 1)) (eJ.f q) (eJ.comm (q - 1) q))))
    (hJoutInj : ∀ n : ℕ, Injective ((image (J.d (q - 1) q)).X n))
    (y : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.cycles p) ⟶ J.cycles p)
    (hy : F.map ((HomologicalComplex.cyclesMap eI p).f 0) ≫ y.f 0 ≫
          (J.iCycles p).f 0 =
        F.map
          ((((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K).iCycles p |>.f 0) ≫
          F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).hom ≫
          u.f p ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0) :
    ∃ x : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p) ⟶ J.X p,
      (F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
          (eI.f p).f 0) ≫ x.f 0 =
        u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0) ∧
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.iCycles p) ≫ x =
        y ≫ J.iCycles p := by
  subst q
  have hp : p + 1 - 1 = p := by omega
  rw [hp] at hIout hJout hJoutInj
  obtain ⟨a, b, f, δ, γ, ha₁, hb₁, ha₂, hb₂⟩ :=
    exists_cartanEilenberg_comparison_augmented_rows F K L u p I eI hIcol hIcycles
      hIout J eJ hJcol hJcycles hJout
  let := a.quasiIso₁
  let := a.quasiIso₂
  let := a.quasiIso₃
  let JA : InjectiveResolution b.base.X₁ :=
    { cocomplex := J.cycles p
      injective := hJcyclesInj
      ι := b.augmentation.τ₁
      quasiIso := b.quasiIso₁ }
  let JB : InjectiveResolution b.base.X₂ :=
    { cocomplex := J.X p
      injective := hJinj
      ι := b.augmentation.τ₂
      quasiIso := b.quasiIso₂ }
  let JC : InjectiveResolution b.base.X₃ :=
    { cocomplex := image (J.d p (p + 1))
      injective := hJoutInj
      ι := b.augmentation.τ₃
      quasiIso := b.quasiIso₃ }
  let c := InjectiveResolution.descOfQuasiIso f.τ₃ JC a.augmentation.τ₃
  have hc : a.augmentation.τ₃ ≫ c = (CochainComplex.single₀ B).map f.τ₃ ≫ JC.ι :=
    InjectiveResolution.descOfQuasiIso_commutes _ _ _
  have hy' : a.augmentation.τ₁ ≫ y = (CochainComplex.single₀ B).map f.τ₁ ≫ JA.ι := by
    apply HomologicalComplex.from_single_hom_ext
    apply (cancel_mono ((J.iCycles p).f 0)).1
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [ha₁, Category.assoc, hy]
    exact hb₁.symm
  obtain ⟨x, hx, hi, _⟩ := InjectiveResolution.exists_horseshoe_morphism_lift_exact_source
    a.base b.base a.base_shortExact b.base_shortExact f
    _ _ _ a.augmentation.τ₁ a.augmentation.τ₂ a.augmentation.τ₃
    _ _ ((cartanEilenbergCycleObjectRow I p).map
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).zero
    a.augmentation.comm₁₂ a.augmentation.comm₂₃
    (fun n ↦ ((cycleObjectRow_shortExact I p).map_of_exact
      (F.mapHomologicalComplex (ComplexShape.up ℕ))).map_of_exact
        (HomologicalComplex.eval B (ComplexShape.up ℕ) n))
    JA JB JC _ _ (cartanEilenbergCycleObjectRow J p).zero
    b.augmentation.comm₁₂ b.augmentation.comm₂₃
    (fun n ↦ (cycleObjectRow_shortExact J p).map_of_exact
      (HomologicalComplex.eval B (ComplexShape.up ℕ) n))
    y c hy' hc
  refine ⟨x, ?_, hi⟩
  have hx₀ := congrArg (fun k ↦ k.f 0) hx
  change a.augmentation.τ₂.f 0 ≫ x.f 0 =
    ((CochainComplex.single₀ B).map f.τ₂).f 0 ≫ b.augmentation.τ₂.f 0 at hx₀
  rw [ha₂, Category.assoc, hx₀]
  exact hb₂


end CategoryTheory
