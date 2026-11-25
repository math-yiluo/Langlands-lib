/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Augmented cycle/object/image rows

Source: Stacks Project, Tags 015I and 015K, the second alternating short exact row.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The kernel/object/image row of a bicomplex in horizontal degree `p`.
Source: Stacks Project, Tag 015I, the cycle/object/outgoing-boundary row. -/
noncomputable def cartanEilenbergCycleObjectRow
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ)) (p : ℤ) :
    ShortComplex (CochainComplex A ℕ) :=
  ShortComplex.mk (I.iCycles p) (factorThruImage (I.d p (p + 1))) (by
    rw [← cancel_mono (image.ι (I.d p (p + 1))), Category.assoc,
      image.fac, HomologicalComplex.iCycles_d, zero_comp])

/-- A row of augmented resolutions, with its short exact base row.
Source: Stacks Project, Tags 015I and 015K. No injectivity is included in this data. -/
structure CartanEilenbergAugmentedRow
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (R : ShortComplex (CochainComplex B ℕ)) where
  /-- The row of objects being resolved. -/
  base : ShortComplex B
  /-- Exactness of the base row. -/
  base_shortExact : base.ShortExact
  /-- The three augmentations and their row squares. -/
  augmentation : base.map (CochainComplex.single₀ B) ⟶ R
  /-- Exactness of the first augmented column. -/
  quasiIso₁ : QuasiIso augmentation.τ₁
  /-- Exactness of the middle augmented column. -/
  quasiIso₂ : QuasiIso augmentation.τ₂
  /-- Exactness of the last augmented column. -/
  quasiIso₃ : QuasiIso augmentation.τ₃

/-- The cycle/object/image row is short exact for any complex shape.
Source: Stacks Project, Tag 015I; the kernel/image factorization in an abelian category. -/
private theorem row_shortExact
    {A : Type*} [Category A] [Abelian A] {ι : Type*} {c : ComplexShape ι}
    (I : HomologicalComplex A c) (p q : ι) (hq : c.next p = q) :
    (ShortComplex.mk (I.iCycles p) (factorThruImage (I.d p q)) (by
      rw [← cancel_mono (image.ι (I.d p q)), Category.assoc,
        image.fac, HomologicalComplex.iCycles_d, zero_comp])).ShortExact := by
  let R := ShortComplex.mk (I.iCycles p) (factorThruImage (I.d p q)) (by
    rw [← cancel_mono (image.ι (I.d p q)), Category.assoc,
      image.fac, HomologicalComplex.iCycles_d, zero_comp])
  change R.ShortExact
  exact
    { exact := R.exact_of_f_is_kernel
        (isKernelOfComp (image.ι (I.d p q)) (I.d p q)
          (I.cyclesIsKernel p q hq) R.zero (image.fac (I.d p q)))
      mono_f := by change Mono (I.iCycles p); infer_instance
      epi_g := by change Epi (factorThruImage (I.d p q)); infer_instance }

private theorem single_iso_exists
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (C : CochainComplex A ℕ) (hC : ∀ n, n ≠ 0 → IsZero (C.X n)) :
    ∃ i : (CochainComplex.single₀ A).obj (C.X 0) ≅ C, i.hom.f 0 = 𝟙 _ := by
  let f := (CochainComplex.fromSingle₀Equiv C (C.X 0)).symm
    ⟨𝟙 _, by simpa using (hC 1 (by omega)).eq_of_tgt (C.d 0 1) 0⟩
  have hf : f.f 0 = 𝟙 _ := by simp [f]
  have : IsIso f := by
    have : ∀ n, IsIso (f.f n) := by
      intro n
      by_cases hn : n = 0
      · subst n
        rw [hf]
        infer_instance
      · exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℕ) 0 (C.X 0) n hn).isIso (hC n hn) (f.f n)
    exact HomologicalComplex.Hom.isIso_of_components f
  exact ⟨asIso f, hf⟩

private theorem row_single_iso_exists
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (R : ShortComplex (CochainComplex A ℕ))
    (h₁ : ∀ n, n ≠ 0 → IsZero (R.X₁.X n))
    (h₂ : ∀ n, n ≠ 0 → IsZero (R.X₂.X n))
    (h₃ : ∀ n, n ≠ 0 → IsZero (R.X₃.X n)) :
    ∃ i : (R.map (HomologicalComplex.eval A (ComplexShape.up ℕ) 0)).map
        (CochainComplex.single₀ A) ≅ R,
      i.hom.τ₁.f 0 = 𝟙 _ ∧ i.hom.τ₂.f 0 = 𝟙 _ ∧ i.hom.τ₃.f 0 = 𝟙 _ := by
  obtain ⟨i₁, hi₁⟩ := single_iso_exists R.X₁ h₁
  obtain ⟨i₂, hi₂⟩ := single_iso_exists R.X₂ h₂
  obtain ⟨i₃, hi₃⟩ := single_iso_exists R.X₃ h₃
  have h₁₂ : (CochainComplex.single₀ A).map (R.f.f 0) ≫ i₂.hom = i₁.hom ≫ R.f := by
    apply HomologicalComplex.from_single_hom_ext
    simp [hi₁, hi₂]
  have h₂₃ : (CochainComplex.single₀ A).map (R.g.f 0) ≫ i₃.hom = i₂.hom ≫ R.g := by
    apply HomologicalComplex.from_single_hom_ext
    simp [hi₂, hi₃]
  let i : (R.map (HomologicalComplex.eval A (ComplexShape.up ℕ) 0)).map
      (CochainComplex.single₀ A) ≅ R :=
    ShortComplex.isoMk i₁ i₂ i₃ h₁₂.symm h₂₃.symm
  exact ⟨i, hi₁, hi₂, hi₃⟩

private noncomputable def row_map
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {I J : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (e : I ⟶ J) (p : ℤ) :
    cartanEilenbergCycleObjectRow I p ⟶ cartanEilenbergCycleObjectRow J p where
  τ₁ := HomologicalComplex.cyclesMap e p
  τ₂ := e.f p
  τ₃ := image.map (Arrow.homMk' (e.f p) (e.f (p + 1)) (e.comm p (p + 1)))
  comm₁₂ := HomologicalComplex.cyclesMap_i e p
  comm₂₃ := (image.factor_map
    (Arrow.homMk' (e.f p) (e.f (p + 1)) (e.comm p (p + 1)))).symm

private theorem row_single_concentrated
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (K : CochainComplex A ℤ) (p : ℤ) :
    let R := cartanEilenbergCycleObjectRow
      (((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) p
    (∀ n, n ≠ 0 → IsZero (R.X₁.X n)) ∧
      (∀ n, n ≠ 0 → IsZero (R.X₂.X n)) ∧
      (∀ n, n ≠ 0 → IsZero (R.X₃.X n)) := by
  dsimp only
  let U := ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact IsZero.of_mono ((U.iCycles p).f n)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (K.X p) n hn)
  · intro n hn
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (K.X p) n hn
  · intro n hn
    exact IsZero.of_epi ((factorThruImage (U.d p (p + 1))).f n)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (K.X p) n hn)

/-- Present the cycle/object/outgoing-image rows as augmented short exact rows,
with the degree-zero identifications needed to transport a base complex map.
This statement constructs rows and identifies augmentations; it constructs no
comparison map between the resolution columns and assumes no injectivity.

Source: Stacks Project, Tags 015I and 015K, alternating short exact rows and their
naturality (blueprint: lem-weil-pbc-ce-comparison-augmented-rows).

Proof: In the abelian category of resolution complexes the cycle inclusion is the
kernel of the outgoing differential, and its factorization through its image is an
epimorphism. Thus the cycle/object/image row is short exact. Evaluation is exact,
and the exact additive functor F preserves these short exact rows. Apply the same
construction to the single-degree-zero bicomplexes on K and L. Their rows are the
single complexes on cycles, objects, and outgoing images of K and L: the single
functor is exact, so its kernel and image comparison maps are isomorphisms. The
isomorphism between applying F to a single complex and the single complex on F
identifies the source base row with F of the row for K. Transport eI and eJ along
these isomorphisms to obtain the two augmentation morphisms. Their components
are quasi-isomorphisms by the six assumed quasi-isomorphisms, exactness of F,
and invariance under isomorphisms. The map on the base rows is induced by u on
cycles, objects and outgoing images. Its two squares follow respectively from
cyclesMap_i and naturality of factorThruImage. Evaluating the transported cycle
augmentation in degree zero gives the first equation. Evaluating the cycle
naturality square gives the second. Evaluating the middle augmentation and its
naturality square gives the last two equations. These identifications are valid
also for zero objects and zero differentials; no epimorphism or monomorphism of
u, and no injectivity or comparison choices, are used. -/
theorem exists_cartanEilenberg_comparison_augmented_rows
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIcol : QuasiIso (eI.f p))
    (hIcycles : QuasiIso (HomologicalComplex.cyclesMap eI p))
    (hIout : QuasiIso
      (image.map (Arrow.homMk' (eI.f p) (eI.f (p + 1)) (eI.comm p (p + 1)))))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJcol : QuasiIso (eJ.f p))
    (hJcycles : QuasiIso (HomologicalComplex.cyclesMap eJ p))
    (hJout : QuasiIso
      (image.map (Arrow.homMk' (eJ.f p) (eJ.f (p + 1)) (eJ.comm p (p + 1))))) :
    ∃ (a : CartanEilenbergAugmentedRow ((cartanEilenbergCycleObjectRow I p).map
        (F.mapHomologicalComplex (ComplexShape.up ℕ))))
      (b : CartanEilenbergAugmentedRow (cartanEilenbergCycleObjectRow J p))
      (f : a.base ⟶ b.base)
      (δ : ((CochainComplex.single₀ B).obj a.base.X₁).X 0 ≅
        F.obj (((((CochainComplex.single₀ A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).cycles p).X 0))
      (γ : F.obj (K.X p) ≅ ((CochainComplex.single₀ B).obj a.base.X₂).X 0),
      a.augmentation.τ₁.f 0 = δ.hom ≫ F.map ((HomologicalComplex.cyclesMap eI p).f 0) ∧
      ((CochainComplex.single₀ B).map f.τ₁).f 0 ≫ b.augmentation.τ₁.f 0 ≫
        (J.iCycles p).f 0 =
        δ.hom ≫ F.map
          (((((CochainComplex.single₀ A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).iCycles p).f 0) ≫
          F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).hom ≫
          u.f p ≫ (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 (L.X p)).inv ≫ (eJ.f p).f 0 ∧
      F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
        (eI.f p).f 0) = γ.hom ≫ a.augmentation.τ₂.f 0 ∧
      γ.hom ≫ ((CochainComplex.single₀ B).map f.τ₂).f 0 ≫ b.augmentation.τ₂.f 0 =
        u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0 := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let E := HomologicalComplex.eval B (ComplexShape.up ℕ) 0
  let U := ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let V := ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let R := (cartanEilenbergCycleObjectRow U p).map G
  let T := cartanEilenbergCycleObjectRow V p
  have hR : R.ShortExact := (row_shortExact U p (p + 1) (by simp)).map_of_exact G
  have hT : T.ShortExact := row_shortExact V p (p + 1) (by simp)
  have hS := hR.map_of_exact E
  have hW := hT.map_of_exact E
  obtain ⟨hU₁, hU₂, hU₃⟩ := row_single_concentrated K p
  obtain ⟨hV₁, hV₂, hV₃⟩ := row_single_concentrated L p
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := row_single_iso_exists R
    (fun n hn ↦ F.map_isZero (hU₁ n hn))
    (fun n hn ↦ F.map_isZero (hU₂ n hn))
    (fun n hn ↦ F.map_isZero (hU₃ n hn))
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := row_single_iso_exists T hV₁ hV₂ hV₃
  let e := (G.mapShortComplex).map (row_map eI p)
  let d := row_map eJ p
  let a : CartanEilenbergAugmentedRow ((cartanEilenbergCycleObjectRow I p).map G) :=
    { base := R.map E
      base_shortExact := hS
      augmentation := i.hom ≫ e
      quasiIso₁ := by
        let := hIcycles
        change QuasiIso (i.hom.τ₁ ≫ G.map (HomologicalComplex.cyclesMap eI p))
        infer_instance
      quasiIso₂ := by
        let := hIcol
        change QuasiIso (i.hom.τ₂ ≫ G.map (eI.f p))
        infer_instance
      quasiIso₃ := by
        let := hIout
        change QuasiIso (i.hom.τ₃ ≫ G.map
          (image.map (Arrow.homMk' (eI.f p) (eI.f (p + 1)) (eI.comm p (p + 1)))))
        infer_instance }
  let b : CartanEilenbergAugmentedRow (cartanEilenbergCycleObjectRow J p) :=
    { base := T.map E
      base_shortExact := hW
      augmentation := j.hom ≫ d
      quasiIso₁ := by
        let := hJcycles
        change QuasiIso (j.hom.τ₁ ≫ HomologicalComplex.cyclesMap eJ p)
        infer_instance
      quasiIso₂ := by
        let := hJcol
        change QuasiIso (j.hom.τ₂ ≫ eJ.f p)
        infer_instance
      quasiIso₃ := by
        let := hJout
        change QuasiIso (j.hom.τ₃ ≫
          image.map (Arrow.homMk' (eJ.f p) (eJ.f (p + 1)) (eJ.comm p (p + 1))))
        infer_instance }
  have ha₁ : a.augmentation.τ₁.f 0 = F.map ((HomologicalComplex.cyclesMap eI p).f 0) := by
    change i.hom.τ₁.f 0 ≫ F.map ((HomologicalComplex.cyclesMap eI p).f 0) = _
    rw [hi₁, Category.id_comp]
  have ha₂ : a.augmentation.τ₂.f 0 = F.map ((eI.f p).f 0) := by
    change i.hom.τ₂.f 0 ≫ F.map ((eI.f p).f 0) = _
    rw [hi₂, Category.id_comp]
  have hb₁ : b.augmentation.τ₁.f 0 = (HomologicalComplex.cyclesMap eJ p).f 0 := by
    change j.hom.τ₁.f 0 ≫ (HomologicalComplex.cyclesMap eJ p).f 0 = _
    rw [hj₁, Category.id_comp]
  have hb₂ : b.augmentation.τ₂.f 0 = (eJ.f p).f 0 := by
    change j.hom.τ₂.f 0 ≫ (eJ.f p).f 0 = _
    rw [hj₂, Category.id_comp]
  have hz : a.base.f ≫ u.f p ≫ b.base.g = 0 := by
    change F.map ((U.iCycles p).f 0) ≫ u.f p ≫
      (factorThruImage (V.d p (p + 1))).f 0 = 0
    apply (cancel_mono ((image.ι (V.d p (p + 1))).f 0)).1
    rw [zero_comp, Category.assoc, Category.assoc]
    have hf := congrArg (fun k ↦ k.f 0) (image.fac (V.d p (p + 1)))
    change (factorThruImage (V.d p (p + 1))).f 0 ≫
      (image.ι (V.d p (p + 1))).f 0 = (V.d p (p + 1)).f 0 at hf
    rw [hf]
    change F.map ((U.iCycles p).f 0) ≫ u.f p ≫
      ((CochainComplex.single₀ B).map (L.d p (p + 1))).f 0 = 0
    rw [CochainComplex.single₀_map_f_zero, u.comm p (p + 1), ← Category.assoc]
    have hk := congrArg (fun k ↦ k.f 0) (U.iCycles_d p (p + 1))
    change (U.iCycles p).f 0 ≫
      ((CochainComplex.single₀ A).map (K.d p (p + 1))).f 0 = 0 at hk
    rw [CochainComplex.single₀_map_f_zero] at hk
    change (F.map ((U.iCycles p).f 0) ≫ F.map (K.d p (p + 1))) ≫ u.f (p + 1) = 0
    rw [← F.map_comp, hk, F.map_zero, zero_comp]
  let := hW.mono_f
  have hzlift : (a.base.f ≫ u.f p) ≫ b.base.g = 0 := by
    simpa only [Category.assoc] using hz
  let x := hW.exact.lift (a.base.f ≫ u.f p) hzlift
  have hx : x ≫ b.base.f = a.base.f ≫ u.f p := hW.exact.lift_f _ hzlift
  have hz' : a.base.f ≫ (u.f p ≫ b.base.g) = 0 := hz
  let := hS.epi_g
  let z := hS.exact.desc (u.f p ≫ b.base.g) hz'
  have hzcomm : a.base.g ≫ z = u.f p ≫ b.base.g := hS.exact.g_desc _ hz'
  let f : a.base ⟶ b.base :=
    { τ₁ := x
      τ₂ := u.f p
      τ₃ := z
      comm₁₂ := hx
      comm₂₃ := hzcomm.symm }
  refine ⟨a, b, f, Iso.refl _, Iso.refl _, ?_, ?_, ?_, ?_⟩
  · simpa using ha₁
  · rw [CochainComplex.single₀_map_f_zero]
    change x ≫ b.augmentation.τ₁.f 0 ≫ (J.iCycles p).f 0 =
      𝟙 _ ≫ F.map ((U.iCycles p).f 0) ≫ F.map (𝟙 _) ≫
        u.f p ≫ 𝟙 _ ≫ (eJ.f p).f 0
    rw [hb₁, Functor.map_id, Category.id_comp, Category.id_comp, Category.id_comp]
    have hc := congrArg (fun k ↦ k.f 0) (HomologicalComplex.cyclesMap_i eJ p)
    change (HomologicalComplex.cyclesMap eJ p).f 0 ≫ (J.iCycles p).f 0 =
      (V.iCycles p).f 0 ≫ (eJ.f p).f 0 at hc
    rw [hc, ← Category.assoc]
    change x ≫ (V.iCycles p).f 0 = F.map ((U.iCycles p).f 0) ≫ u.f p at hx
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ (eJ.f p).f 0) hx
  · simpa using ha₂.symm
  · simp [f, hb₂]

end CategoryTheory
