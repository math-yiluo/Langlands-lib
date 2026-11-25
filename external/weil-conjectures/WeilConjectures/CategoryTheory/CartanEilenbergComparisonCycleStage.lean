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
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource

/-! # The cycle stage of a Cartan–Eilenberg comparison

Source: Stacks Project, Tags 015I and 015K, with the lifting property of Tag 013P(2).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory



private noncomputable def bi {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) : image (K.d (p - 1) p) ⟶ K.cycles p :=
  K.liftCycles (image.ι (K.d (p - 1) p)) (p + 1) (by simp) (by
    apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
    simp)

@[reassoc (attr := simp)]
private lemma bi_fac {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) :
    bi K p ≫ K.iCycles p = image.ι (K.d (p - 1) p) := by
  simp [bi]

@[reassoc (attr := simp)]
private lemma bi_factor {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) :
    factorThruImage (K.d (p - 1) p) ≫ bi K p = K.toCycles (p - 1) p := by
  apply (cancel_mono (K.iCycles p)).1
  simp

@[reassoc (attr := simp)]
private lemma bi_zero {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) : bi K p ≫ K.homologyπ p = 0 := by
  apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
  simp [← Category.assoc]

private noncomputable def row {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (bi K p) (K.homologyπ p) (bi_zero K p)

private lemma row_exact {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) : (row K p).ShortExact := by
  have he : (ShortComplex.mk (K.toCycles (p - 1) p) (K.homologyπ p)
      (K.toCycles_comp_homologyπ (p - 1) p)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (p - 1) p (by simp))
  let φ : ShortComplex.mk (K.toCycles (p - 1) p) (K.homologyπ p)
      (K.toCycles_comp_homologyπ (p - 1) p) ⟶ row K p :=
    { τ₁ := factorThruImage (K.d (p - 1) p)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [row]
      comm₂₃ := by simp [row] }
  have hm : Mono (row K p).f := mono_of_mono_fac (bi_fac K p)
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 he
          mono_f := hm
          epi_g := by dsimp [row]; infer_instance }

private noncomputable def hiso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (K : CochainComplex C ℤ) (p : ℤ) :
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology p ≅
      H.obj (K.homology p) :=
  ((K.sc p).leftHomologyData.map H).homologyIso ≪≫
    H.mapIso (K.sc p).leftHomologyIso

private lemma hiso_π {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (K : CochainComplex C ℤ) (p : ℤ) :
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ p ≫
      (hiso H K p).hom = ((K.sc p).mapCyclesIso H).hom ≫ H.map (K.homologyπ p) := by
  change ((K.sc p).map H).homologyπ ≫
    (((K.sc p).leftHomologyData.map H).homologyIso.hom ≫
      H.map (K.sc p).leftHomologyIso.hom) =
    ((K.sc p).leftHomologyData.map H).cyclesIso.hom ≫ H.map (K.sc p).homologyπ
  rw [← Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, Category.assoc]
  change ((K.sc p).leftHomologyData.map H).cyclesIso.hom ≫
    H.map (K.sc p).leftHomologyData.π ≫ H.map (K.sc p).leftHomologyIso.hom = _
  rw [← H.map_comp]
  rfl

private noncomputable def rowMap {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (v : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ) :
    (row K p).map H ⟶ row L p where
  τ₁ := (PreservesImage.iso H (K.d (p - 1) p)).inv ≫
    image.map (Arrow.homMk' (v.f (p - 1)) (v.f p) (v.comm (p - 1) p))
  τ₂ := ((K.sc p).mapCyclesIso H).inv ≫ HomologicalComplex.cyclesMap v p
  τ₃ := (hiso H K p).inv ≫ HomologicalComplex.homologyMap v p
  comm₁₂ := by
    dsimp [row]
    apply (cancel_mono (L.iCycles p)).1
    simp only [Category.assoc, bi_fac, HomologicalComplex.cyclesMap_i]
    have hc : ((K.sc p).mapCyclesIso H).inv ≫
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles p =
          H.map (K.iCycles p) := by
      change ((K.sc p).mapCyclesIso H).inv ≫ ((K.sc p).map H).iCycles = _
      rw [← (K.sc p).mapCyclesIso_hom_iCycles H, Iso.inv_hom_id_assoc]
      rfl
    change (PreservesImage.iso H (K.d (p - 1) p)).inv ≫ _ =
      H.map (bi K p) ≫ ((K.sc p).mapCyclesIso H).inv ≫ _
    rw [reassoc_of% hc, ← H.map_comp_assoc, bi_fac]
    change (PreservesImage.iso H (K.d (p - 1) p)).inv ≫
      image.map (Arrow.homMk' (f := H.map (K.d (p - 1) p))
        (v.f (p - 1)) (v.f p) (v.comm (p - 1) p)) ≫ image.ι (L.d (p - 1) p) = _
    rw [image.map_homMk'_ι, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ v.f p)
      (PreservesImage.inv_comp_image_ι_map H (K.d (p - 1) p))
  comm₂₃ := by
    dsimp [row]
    rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality,
      ← Category.assoc]
    have hh : ((K.sc p).mapCyclesIso H).inv ≫
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ p =
          H.map (K.homologyπ p) ≫ (hiso H K p).inv := by
      apply (cancel_mono (hiso H K p).hom).1
      rw [Category.assoc, hiso_π, Iso.inv_hom_id_assoc]
      simp
    rw [hh]
    simp only [Category.assoc]

private noncomputable def rowHom {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (v : K ⟶ L) (p : ℤ) : row K p ⟶ row L p where
  τ₁ := image.map (Arrow.homMk' (v.f (p - 1)) (v.f p) (v.comm (p - 1) p))
  τ₂ := HomologicalComplex.cyclesMap v p
  τ₃ := HomologicalComplex.homologyMap v p
  comm₁₂ := by
    dsimp [row]
    apply (cancel_mono (L.iCycles p)).1
    simp only [Category.assoc, bi_fac, HomologicalComplex.cyclesMap_i]
    rw [image.map_homMk'_ι, ← Category.assoc, bi_fac]
  comm₂₃ := by exact (HomologicalComplex.homologyπ_naturality v p).symm

private noncomputable def supportedIso {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, n ≠ 0 → IsZero (K.X n)) :
    (CochainComplex.single₀ C).obj (K.X 0) ≅ K := by
  let φ : (CochainComplex.single₀ C).obj (K.X 0) ⟶ K :=
    (CochainComplex.fromSingle₀Equiv K (K.X 0)).symm
      ⟨𝟙 _, by simpa using (hK 1 (by decide)).eq_of_tgt (K.d 0 1) 0⟩
  have (n : ℕ) : IsIso (φ.f n) := by
    cases n with
    | zero =>
      dsimp [φ]
      simp only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      infer_instance
    | succ n =>
      exact IsZero.isIso
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
        (hK (n + 1) (by omega)) _
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  exact asIso φ

@[simp]
private lemma supportedIso_zero {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, n ≠ 0 → IsZero (K.X n)) :
    (supportedIso K hK).hom.f 0 = 𝟙 _ := by
  simp [supportedIso]

private lemma supportedIso_naturality {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℕ}
    (hK : ∀ n : ℕ, n ≠ 0 → IsZero (K.X n))
    (hL : ∀ n : ℕ, n ≠ 0 → IsZero (L.X n)) (f : K ⟶ L) :
    (CochainComplex.single₀ C).map (f.f 0) ≫ (supportedIso L hL).hom =
      (supportedIso K hK).hom ≫ f := by
  apply HomologicalComplex.from_single_hom_ext
  simp

private noncomputable def singleComparison {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L where
  f p := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).hom.app
      (K.X p) ≫ (CochainComplex.single₀ B).map (u.f p)
  comm' p q _ := by
    change ((HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℕ) 0).hom.app (K.X p) ≫
      (CochainComplex.single₀ B).map (u.f p)) ≫
      (CochainComplex.single₀ B).map (L.d p q) =
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((CochainComplex.single₀ A).map (K.d p q)) ≫ _
    rw [Category.assoc, ← Functor.map_comp, u.comm, Functor.map_comp,
      ← Category.assoc]
    simpa only [Functor.comp_map, Functor.mapHomologicalComplex_obj_d, Category.assoc] using
      congrArg (fun t ↦ t ≫ (CochainComplex.single₀ B).map (u.f q))
      ((HomologicalComplex.singleMapHomologicalComplex F
        (ComplexShape.up ℕ) 0).hom.naturality (K.d p q)).symm


private lemma rowMap_i {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (v : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ) :
    (rowMap H v p).τ₂ ≫ L.iCycles p = H.map (K.iCycles p) ≫ v.f p := by
  change (((K.sc p).mapCyclesIso H).inv ≫ HomologicalComplex.cyclesMap v p) ≫ _ = _
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]
  have hc : ((K.sc p).mapCyclesIso H).inv ≫
      ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles p =
        H.map (K.iCycles p) := by
    change ((K.sc p).mapCyclesIso H).inv ≫ ((K.sc p).map H).iCycles = _
    rw [← (K.sc p).mapCyclesIso_hom_iCycles H, Iso.inv_hom_id_assoc]
    rfl
  rw [hc]

private lemma rowMap_factor {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (v : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ) :
    H.map (factorThruImage (K.d (p - 1) p)) ≫ (rowMap H v p).τ₁ =
      v.f (p - 1) ≫ factorThruImage (L.d (p - 1) p) := by
  apply (cancel_mono (image.ι (L.d (p - 1) p))).1
  change (H.map (factorThruImage (K.d (p - 1) p)) ≫
    ((PreservesImage.iso H (K.d (p - 1) p)).inv ≫ image.map
      (Arrow.homMk' (f := H.map (K.d (p - 1) p))
        (v.f (p - 1)) (v.f p) (v.comm (p - 1) p)))) ≫ _ = _
  simp only [Category.assoc, image.map_homMk'_ι, image.fac]
  rw [← Category.assoc (PreservesImage.iso H _).inv,
    PreservesImage.inv_comp_image_ι_map, ← H.map_comp_assoc, image.fac]
  exact (v.comm (p - 1) p).symm

private lemma rowHom_factor {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (e : K ⟶ L) (p : ℤ) :
    factorThruImage (K.d (p - 1) p) ≫ (rowHom e p).τ₁ =
      e.f (p - 1) ≫ factorThruImage (L.d (p - 1) p) := by
  apply (cancel_mono (image.ι (L.d (p - 1) p))).1
  change (_ ≫ image.map (Arrow.homMk' (e.f (p - 1)) (e.f p)
    (e.comm (p - 1) p))) ≫ _ = _
  rw [Category.assoc, image.map_homMk'_ι, ← Category.assoc, image.fac,
    Category.assoc, image.fac, e.comm]

/-- A presentation of two augmented boundary/cycle/homology rows over their coefficient
objects. This contains only the original row maps and augmentations, together with their
exactness and naturality; it contains no comparison between the resolution columns.
The coefficient rows can be taken to be the image of the row of `K` under `F` and the
row of `L`, respectively. -/
private structure CartanEilenbergCycleRowPresentation
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (p : ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    where
  /-- The source coefficient row. -/
  S : ShortComplex B
  /-- The target coefficient row. -/
  T : ShortComplex B
  /-- Exactness of the source coefficient row. -/
  source_exact : S.ShortExact
  /-- Exactness of the target coefficient row. -/
  target_exact : T.ShortExact
  /-- The coefficient-row morphism induced by `u`. -/
  f : S ⟶ T
  /-- The boundary augmentation, transported to a single complex. -/
  sA : (CochainComplex.single₀ B).obj S.X₁ ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (image (I.d (p - 1) p))
  /-- The cycle augmentation, transported to a single complex. -/
  sB : (CochainComplex.single₀ B).obj S.X₂ ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.cycles p)
  /-- The homology augmentation, transported to a single complex. -/
  sC : (CochainComplex.single₀ B).obj S.X₃ ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.homology p)
  /-- Exactness of the augmented source boundary column. -/
  source_boundary_quasiIso : QuasiIso sA
  /-- Exactness of the augmented source cycle column. -/
  source_cycle_quasiIso : QuasiIso sB
  /-- Exactness of the augmented source homology column. -/
  source_homology_quasiIso : QuasiIso sC
  /-- The source boundary inclusion after applying `F`. -/
  i : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (image (I.d (p - 1) p)) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.cycles p)
  /-- The source homology projection after applying `F`. -/
  π : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.cycles p) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.homology p)
  /-- The source row is a complex. -/
  iπ : i ≫ π = 0
  /-- The source boundary augmentation square. -/
  hi : sA ≫ i = (CochainComplex.single₀ B).map S.f ≫ sB
  /-- The source homology augmentation square. -/
  hπ : sB ≫ π = (CochainComplex.single₀ B).map S.g ≫ sC
  /-- Degreewise exactness of the source row. -/
  source_rows_exact : ∀ n : ℕ,
    ((ShortComplex.mk i π iπ).map
      (HomologicalComplex.eval B (ComplexShape.up ℕ) n)).ShortExact
  /-- The target boundary augmentation. -/
  tA : (CochainComplex.single₀ B).obj T.X₁ ⟶ image (J.d (p - 1) p)
  /-- The target cycle augmentation. -/
  tB : (CochainComplex.single₀ B).obj T.X₂ ⟶ J.cycles p
  /-- The target homology augmentation. -/
  tC : (CochainComplex.single₀ B).obj T.X₃ ⟶ J.homology p
  /-- Exactness of the augmented target boundary column. -/
  target_boundary_quasiIso : QuasiIso tA
  /-- Exactness of the augmented target cycle column. -/
  target_cycle_quasiIso : QuasiIso tB
  /-- Exactness of the augmented target homology column. -/
  target_homology_quasiIso : QuasiIso tC
  /-- The target boundary inclusion. -/
  α : image (J.d (p - 1) p) ⟶ J.cycles p
  /-- The target homology projection. -/
  β : J.cycles p ⟶ J.homology p
  /-- The target row is a complex. -/
  αβ : α ≫ β = 0
  /-- The target boundary augmentation square. -/
  hα : tA ≫ α = (CochainComplex.single₀ B).map T.f ≫ tB
  /-- The target homology augmentation square. -/
  hβ : tB ≫ β = (CochainComplex.single₀ B).map T.g ≫ tC
  /-- Degreewise exactness of the target row. -/
  target_rows_exact : ∀ n : ℕ,
    ((ShortComplex.mk α β αβ).map
      (HomologicalComplex.eval B (ComplexShape.up ℕ) n)).ShortExact
  /-- The degree-zero identification used to read the cycle augmentation. -/
  source_zero_iso : ((CochainComplex.single₀ B).obj S.X₂).X 0 ≅
    F.obj (((((CochainComplex.single₀ A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).cycles p).X 0)
  /-- The normalized cycle augmentation agrees with the given augmentation. -/
  source_zero : sB.f 0 = source_zero_iso.hom ≫
    F.map ((HomologicalComplex.cyclesMap eI p).f 0)
  /-- The coefficient cycle square, included into the target object column. -/
  coefficient_zero : ((CochainComplex.single₀ B).map f.τ₂).f 0 ≫ tB.f 0 ≫
      (J.iCycles p).f 0 =
    source_zero_iso.hom ≫
      F.map (((((CochainComplex.single₀ A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).iCycles p).f 0) ≫
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).hom ≫
      u.f p ≫ (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℕ) 0 (L.X p)).inv ≫ (eJ.f p).f 0
  /-- Factoring the incoming differential through the source boundary row. -/
  source_factor : (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (factorThruImage (I.d (p - 1) p)) ≫ i =
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.toCycles (p - 1) p)
  /-- The target boundary map factors the image inclusion. -/
  target_inclusion : α ≫ J.iCycles p = image.ι (J.d (p - 1) p)
  /-- Cancelling the coefficient boundary epimorphism converts the displayed assumption
  on the incoming object column into the boundary augmentation square. -/
  boundary_square : ∀
      (b : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (image (I.d (p - 1) p)) ⟶ image (J.d (p - 1) p)),
    F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
      (K.X (p - 1))).inv ≫ (eI.f (p - 1)).f 0 ≫
        (factorThruImage (I.d (p - 1) p)).f 0) ≫ b.f 0 =
      u.f (p - 1) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        (L.X (p - 1))).inv ≫ (eJ.f (p - 1)).f 0 ≫
          (factorThruImage (J.d (p - 1) p)).f 0 →
    sA ≫ b = (CochainComplex.single₀ B).map f.τ₁ ≫ tA

/-- Put the two given augmented boundary/cycle/homology rows over single coefficient
complexes, including the coefficient morphism induced by `u`. No injectivity hypothesis
is required, and no lift or comparison between the resolution columns is produced.

Source: Stacks Project, Tag 015I, the rows `B → Z → H`, and Tag 015K, naturality.

Proof: In any abelian category, factor the image inclusion of the incoming differential
through its kernel at the next degree. The sequence from this boundary to cycles to
homology is short exact: the last map is the cokernel of the incoming differential
viewed as a map to cycles, and its image is unchanged by the epimorphism onto boundaries.
Use these rows for K, L, I and J. Evaluation in a resolution degree is exact. Applying F
preserves each short exact row and each given augmented quasi-isomorphism.
The exact single-degree functor preserves the kernels, images and homology of K and L.
Use its canonical preservation isomorphisms, and the natural isomorphism between applying
F to a single complex and taking the single complex of F, to define the six augmentations.
Transport the three quasi-isomorphisms of each augmentation along these isomorphisms.
The coefficient-row map is induced by u on boundaries, cycles and homology; their two
commuting squares follow by image and homology naturality. The same identities applied
to eI and eJ give hi, hπ, hα and hβ. At degree zero, the cycle preservation isomorphism
and singleObjXSelf give source_zero_iso, source_zero and coefficient_zero.
Finally precompose the desired boundary augmentation square at zero with the epimorphism
from F(K.X (p-1)) onto F(boundaries K p). Image naturality turns its two sides into the
assumed equation. Cancel this epimorphism. At every positive degree its source is zero,
so these component equations give the complex equation boundary_square.
The image factorization through cycles gives source_factor and target_inclusion. -/
private theorem exists_cartanEilenberg_cycle_row_presentation
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (p : ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIres :
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJres :
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p)) :
    Nonempty (CartanEilenbergCycleRowPresentation F K L u p I eI J eJ)  := by
  let SK := ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let SL := ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let E := HomologicalComplex.eval B (ComplexShape.up ℕ) 0
  let RS := (row SK p).map G
  let RT := row SL p
  let S := RS.map E
  let T := RT.map E
  let v := singleComparison F K L u
  let f := E.mapShortComplex.map (rowMap G v p)
  let a := G.mapShortComplex.map (rowHom eI p)
  let t := rowHom eJ p
  have hz (n : ℕ) (hn : n ≠ 0) : IsZero ((SK.cycles p).X n) := by
    exact IsZero.of_mono ((SK.iCycles p).f n)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hd (n : ℕ) (hn : n ≠ 0) : IsZero ((image (SK.d (p - 1) p)).X n) := by
    exact IsZero.of_mono ((image.ι (SK.d (p - 1) p)).f n)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hh (n : ℕ) (hn : n ≠ 0) : IsZero ((SK.homology p).X n) := by
    exact IsZero.of_epi ((SK.homologyπ p).f n) (hz n hn)
  have htz (n : ℕ) (hn : n ≠ 0) : IsZero ((SL.cycles p).X n) := by
    exact IsZero.of_mono ((SL.iCycles p).f n)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have htd (n : ℕ) (hn : n ≠ 0) : IsZero ((image (SL.d (p - 1) p)).X n) := by
    exact IsZero.of_mono ((image.ι (SL.d (p - 1) p)).f n)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hth (n : ℕ) (hn : n ≠ 0) : IsZero ((SL.homology p).X n) := by
    exact IsZero.of_epi ((SL.homologyπ p).f n) (htz n hn)
  let nA := supportedIso RS.X₁ (fun n hn ↦ F.map_isZero (hd n hn))
  let nB := supportedIso RS.X₂ (fun n hn ↦ F.map_isZero (hz n hn))
  let nC := supportedIso RS.X₃ (fun n hn ↦ F.map_isZero (hh n hn))
  let mA := supportedIso RT.X₁ htd
  let mB := supportedIso RT.X₂ htz
  let mC := supportedIso RT.X₃ hth
  have : QuasiIso (HomologicalComplex.cyclesMap eI p) := hIres.1
  have : QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p)
      (eI.comm (p - 1) p))) := hIres.2.1
  have : QuasiIso (HomologicalComplex.homologyMap eI p) := hIres.2.2
  have : QuasiIso (HomologicalComplex.cyclesMap eJ p) := hJres.1
  have : QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p)
      (eJ.comm (p - 1) p))) := hJres.2.1
  have : QuasiIso (HomologicalComplex.homologyMap eJ p) := hJres.2.2
  refine ⟨{
    S := S
    T := T
    source_exact := ((row_exact SK p).map_of_exact G).map_of_exact E
    target_exact := (row_exact SL p).map_of_exact E
    f := f
    sA := nA.hom ≫ a.τ₁
    sB := nB.hom ≫ a.τ₂
    sC := nC.hom ≫ a.τ₃
    source_boundary_quasiIso := ?_
    source_cycle_quasiIso := ?_
    source_homology_quasiIso := ?_
    i := G.map (bi I p)
    π := G.map (I.homologyπ p)
    iπ := by rw [← G.map_comp, bi_zero, G.map_zero]
    hi := ?_
    hπ := ?_
    source_rows_exact := fun n ↦ ((row_exact I p).map_of_exact G).map_of_exact
      (HomologicalComplex.eval B (ComplexShape.up ℕ) n)
    tA := mA.hom ≫ t.τ₁
    tB := mB.hom ≫ t.τ₂
    tC := mC.hom ≫ t.τ₃
    target_boundary_quasiIso := ?_
    target_cycle_quasiIso := ?_
    target_homology_quasiIso := ?_
    α := bi J p
    β := J.homologyπ p
    αβ := bi_zero J p
    hα := ?_
    hβ := ?_
    target_rows_exact := fun n ↦ (row_exact J p).map_of_exact
      (HomologicalComplex.eval B (ComplexShape.up ℕ) n)
    source_zero_iso := Iso.refl _
    source_zero := ?_
    coefficient_zero := ?_
    source_factor := by rw [← G.map_comp, bi_factor]
    target_inclusion := bi_fac J p
    boundary_square := ?_
  }⟩
  · change QuasiIso (nA.hom ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))))
    infer_instance
  · change QuasiIso (nB.hom ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (HomologicalComplex.cyclesMap eI p))
    infer_instance
  · change QuasiIso (nC.hom ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (HomologicalComplex.homologyMap eI p))
    infer_instance
  · change (nA.hom ≫ a.τ₁) ≫ G.map (bi I p) =
      (CochainComplex.single₀ B).map (RS.f.f 0) ≫ nB.hom ≫ a.τ₂
    have ha := a.comm₁₂
    change a.τ₁ ≫ G.map (bi I p) = RS.f ≫ a.τ₂ at ha
    rw [Category.assoc, ha, ← Category.assoc]
    rw [← supportedIso_naturality, Category.assoc]
  · change (nB.hom ≫ a.τ₂) ≫ G.map (I.homologyπ p) =
      (CochainComplex.single₀ B).map (RS.g.f 0) ≫ nC.hom ≫ a.τ₃
    have ha := a.comm₂₃
    change a.τ₂ ≫ G.map (I.homologyπ p) = RS.g ≫ a.τ₃ at ha
    rw [Category.assoc, ha, ← Category.assoc]
    rw [← supportedIso_naturality, Category.assoc]
  · change QuasiIso (mA.hom ≫ image.map
      (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p)))
    infer_instance
  · change QuasiIso (mB.hom ≫ HomologicalComplex.cyclesMap eJ p)
    infer_instance
  · change QuasiIso (mC.hom ≫ HomologicalComplex.homologyMap eJ p)
    infer_instance
  · change (mA.hom ≫ t.τ₁) ≫ bi J p =
      (CochainComplex.single₀ B).map (RT.f.f 0) ≫ mB.hom ≫ t.τ₂
    have ht := t.comm₁₂
    change t.τ₁ ≫ bi J p = RT.f ≫ t.τ₂ at ht
    rw [Category.assoc, ht, ← Category.assoc]
    rw [← supportedIso_naturality, Category.assoc]
  · change (mB.hom ≫ t.τ₂) ≫ J.homologyπ p =
      (CochainComplex.single₀ B).map (RT.g.f 0) ≫ mC.hom ≫ t.τ₃
    have ht := t.comm₂₃
    change t.τ₂ ≫ J.homologyπ p = RT.g ≫ t.τ₃ at ht
    rw [Category.assoc, ht, ← Category.assoc]
    rw [← supportedIso_naturality, Category.assoc]
  · change nB.hom.f 0 ≫ F.map ((HomologicalComplex.cyclesMap eI p).f 0) =
      𝟙 _ ≫ F.map ((HomologicalComplex.cyclesMap eI p).f 0)
    rw [show nB.hom.f 0 = 𝟙 _ from supportedIso_zero _ _]
    rfl
  · simp only [HomologicalComplex.comp_f]
    rw [show mB.hom.f 0 = 𝟙 _ from supportedIso_zero _ _]
    dsimp only [f, t, E, S, T, RS, RT, G, rowHom]
    simp only [CochainComplex.single₀_map_f_zero, CochainComplex.single₀ObjXSelf,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    change (rowMap G v p).τ₂.f 0 ≫
      (𝟙 ((SL.cycles p).X 0) ≫ (HomologicalComplex.cyclesMap eJ p).f 0) ≫
        (J.iCycles p).f 0 =
        F.map ((SK.iCycles p).f 0) ≫ F.map (𝟙 (K.X p)) ≫ u.f p ≫
          𝟙 (L.X p) ≫ (eJ.f p).f 0
    erw [Category.id_comp, F.map_id, Category.id_comp]
    have hj := HomologicalComplex.congr_hom (HomologicalComplex.cyclesMap_i eJ p) 0
    change (HomologicalComplex.cyclesMap eJ p).f 0 ≫ (J.iCycles p).f 0 =
      (SL.iCycles p).f 0 ≫ (eJ.f p).f 0 at hj
    have hv := HomologicalComplex.congr_hom (rowMap_i G v p) 0
    change (rowMap G v p).τ₂.f 0 ≫ (SL.iCycles p).f 0 =
      F.map ((SK.iCycles p).f 0) ≫ (v.f p).f 0 at hv
    have hv₀ : (v.f p).f 0 = u.f p := by
      simp only [v, singleComparison, HomologicalComplex.comp_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CochainComplex.single₀_map_f_zero, CochainComplex.single₀ObjXSelf,
        Iso.refl_hom, Iso.refl_inv]
      change (F.map (𝟙 (K.X p)) ≫ 𝟙 (F.obj (K.X p))) ≫ u.f p = u.f p
      rw [F.map_id, Category.id_comp, Category.id_comp]
    erw [Category.assoc, hj, Category.id_comp]
    have h := congrArg (fun q ↦ q ≫ (eJ.f p).f 0) hv
    rw [hv₀] at h
    simpa only [rowMap, HomologicalComplex.comp_f, Category.assoc] using h
  · intro b hb
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    rw [show nA.hom.f 0 = 𝟙 _ from supportedIso_zero _ _,
      show mA.hom.f 0 = 𝟙 _ from supportedIso_zero _ _]
    dsimp only [a, t, f, E, G, rowHom]
    simp only [CochainComplex.single₀_map_f_zero]
    change (𝟙 _ ≫ F.map ((rowHom eI p).τ₁.f 0)) ≫ b.f 0 =
      (rowMap G v p).τ₁.f 0 ≫ (𝟙 _ ≫ (rowHom eJ p).τ₁.f 0)
    erw [Category.id_comp, Category.id_comp]
    have hi₀ := HomologicalComplex.congr_hom (rowHom_factor eI p) 0
    change (factorThruImage (SK.d (p - 1) p)).f 0 ≫ (rowHom eI p).τ₁.f 0 =
      (eI.f (p - 1)).f 0 ≫ (factorThruImage (I.d (p - 1) p)).f 0 at hi₀
    have hj₀ := HomologicalComplex.congr_hom (rowHom_factor eJ p) 0
    change (factorThruImage (SL.d (p - 1) p)).f 0 ≫ (rowHom eJ p).τ₁.f 0 =
      (eJ.f (p - 1)).f 0 ≫ (factorThruImage (J.d (p - 1) p)).f 0 at hj₀
    have hv₀ : (v.f (p - 1)).f 0 = u.f (p - 1) := by
      simp only [v, singleComparison, HomologicalComplex.comp_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CochainComplex.single₀_map_f_zero, CochainComplex.single₀ObjXSelf,
        Iso.refl_hom, Iso.refl_inv]
      change (F.map (𝟙 (K.X (p - 1))) ≫ 𝟙 (F.obj (K.X (p - 1)))) ≫
        u.f (p - 1) = u.f (p - 1)
      rw [F.map_id, Category.id_comp, Category.id_comp]
    have hv := HomologicalComplex.congr_hom (rowMap_factor G v p) 0
    change F.map ((factorThruImage (SK.d (p - 1) p)).f 0) ≫
        (rowMap G v p).τ₁.f 0 =
      (v.f (p - 1)).f 0 ≫ (factorThruImage (SL.d (p - 1) p)).f 0 at hv
    rw [hv₀] at hv
    simp only [CochainComplex.single₀ObjXSelf, Iso.refl_inv] at hb
    change F.map (𝟙 _ ≫ (eI.f (p - 1)).f 0 ≫
      (factorThruImage (I.d (p - 1) p)).f 0) ≫ b.f 0 =
        u.f (p - 1) ≫ 𝟙 _ ≫ (eJ.f (p - 1)).f 0 ≫
          (factorThruImage (J.d (p - 1) p)).f 0 at hb
    erw [Category.id_comp, Category.id_comp] at hb
    apply (cancel_epi (F.map ((factorThruImage (SK.d (p - 1) p)).f 0))).1
    calc
      F.map ((factorThruImage (SK.d (p - 1) p)).f 0) ≫
          F.map ((rowHom eI p).τ₁.f 0) ≫ b.f 0 =
        F.map ((factorThruImage (SK.d (p - 1) p)).f 0 ≫
          (rowHom eI p).τ₁.f 0) ≫ b.f 0 := by rw [F.map_comp, Category.assoc]
      _ = F.map ((eI.f (p - 1)).f 0 ≫
          (factorThruImage (I.d (p - 1) p)).f 0) ≫ b.f 0 := by rw [hi₀]
      _ = u.f (p - 1) ≫ (eJ.f (p - 1)).f 0 ≫
          (factorThruImage (J.d (p - 1) p)).f 0 := hb
      _ = u.f (p - 1) ≫ (factorThruImage (SL.d (p - 1) p)).f 0 ≫
          (rowHom eJ p).τ₁.f 0 := by rw [hj₀]
      _ = F.map ((factorThruImage (SK.d (p - 1) p)).f 0) ≫
          (rowMap G v p).τ₁.f 0 ≫ (rowHom eJ p).τ₁.f 0 := by
        simpa only [Category.assoc] using
          congrArg (fun q ↦ q ≫ (rowHom eJ p).τ₁.f 0) hv.symm


/-- Extend an augmented incoming boundary comparison to the cycles, without choosing
an object-column or outgoing-boundary comparison. The augmentation equation is written after
inclusion into the target object column, so no identification of single-complex cycles is needed.

Source: Stacks Project, Tags 015I, 015K and 013P(2);
(blueprint: lem-weil-pbc-ce-comparison-cycle-stage).

Proof: Form the short exact boundary → cycles → homology rows of the two single
bicomplexes and the resolutions. Apply F to the source rows and evaluate both coefficient
rows in resolution degree zero. Each column of a single bicomplex is supported at zero:
this follows for boundaries and cycles by their inclusions into an object column, and for
homology by the epimorphism from cycles. Hence each coefficient column is canonically
isomorphic to the single complex of its degree-zero object. Transport the augmentations
through these explicit isomorphisms. Exactness and the given quasi-isomorphisms survive
F and evaluation. The single-complex comparison induced by u gives the coefficient-row map.
Cancel the epimorphism onto the source boundary at degree zero to obtain the augmented
boundary square from hb. At positive degrees the coefficient complex is zero.
Bundle the three target columns as injective resolutions. Use descOfQuasiIso to lift
the coefficient homology map, then apply the exact-source horseshoe morphism theorem
with this homology lift and the prescribed boundary map. Its middle map is y.
Include the degree-zero augmentation square into the target object column for the first
formula. Compose the boundary square with the source factorThruImage and target cycle
inclusion for the second formula, using the image factorization through cycles. -/
theorem exists_cartanEilenberg_comparison_cycle_stage
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (p : ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIres :
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJinj' : ∀ n : ℕ,
      Injective ((J.cycles p).X n) ∧
      Injective ((image (J.d (p - 1) p)).X n) ∧
      Injective ((J.homology p).X n))
    (hJres :
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (b : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (image (I.d (p - 1) p)) ⟶ image (J.d (p - 1) p))
    (hb : F.map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X (p - 1))).inv ≫
          (eI.f (p - 1)).f 0 ≫ (factorThruImage (I.d (p - 1) p)).f 0) ≫ b.f 0 =
      u.f (p - 1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X (p - 1))).inv ≫
          (eJ.f (p - 1)).f 0 ≫ (factorThruImage (J.d (p - 1) p)).f 0) :
    ∃ y : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.cycles p) ⟶ J.cycles p,
      (F.map ((HomologicalComplex.cyclesMap eI p).f 0) ≫ y.f 0 ≫
          (J.iCycles p).f 0 =
        F.map
          ((((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K).iCycles p |>.f 0) ≫
          F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).hom ≫
          u.f p ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0) ∧
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.toCycles (p - 1) p) ≫
          y ≫ J.iCycles p =
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (factorThruImage (I.d (p - 1) p)) ≫ b ≫ image.ι (J.d (p - 1) p) := by
  obtain ⟨R⟩ := exists_cartanEilenberg_cycle_row_presentation
    F K L u p I eI hIres J eJ hJres
  have : QuasiIso R.sA := R.source_boundary_quasiIso
  have : QuasiIso R.sB := R.source_cycle_quasiIso
  have : QuasiIso R.sC := R.source_homology_quasiIso
  let JA : InjectiveResolution R.T.X₁ :=
    { cocomplex := image (J.d (p - 1) p)
      injective := fun n ↦ (hJinj' n).2.1
      ι := R.tA
      quasiIso := R.target_boundary_quasiIso }
  let JB : InjectiveResolution R.T.X₂ :=
    { cocomplex := J.cycles p
      injective := fun n ↦ (hJinj' n).1
      ι := R.tB
      quasiIso := R.target_cycle_quasiIso }
  let JC : InjectiveResolution R.T.X₃ :=
    { cocomplex := J.homology p
      injective := fun n ↦ (hJinj' n).2.2
      ι := R.tC
      quasiIso := R.target_homology_quasiIso }
  let c := InjectiveResolution.descOfQuasiIso R.f.τ₃ JC R.sC
  have hc : R.sC ≫ c = (CochainComplex.single₀ B).map R.f.τ₃ ≫ JC.ι :=
    InjectiveResolution.descOfQuasiIso_commutes R.f.τ₃ JC R.sC
  obtain ⟨y, hy, hby, _hyc⟩ :=
    InjectiveResolution.exists_horseshoe_morphism_lift_exact_source
      R.S R.T R.source_exact R.target_exact R.f _ _ _ R.sA R.sB R.sC
      R.i R.π R.iπ R.hi R.hπ R.source_rows_exact
      JA JB JC R.α R.β R.αβ R.hα R.hβ R.target_rows_exact
      b c (R.boundary_square b hb) hc
  refine ⟨y, ?_, ?_⟩
  · have h₀ := HomologicalComplex.congr_hom hy 0
    change R.sB.f 0 ≫ y.f 0 =
      ((CochainComplex.single₀ B).map R.f.τ₂).f 0 ≫ R.tB.f 0 at h₀
    apply (cancel_epi R.source_zero_iso.hom).1
    simpa only [Category.assoc, R.source_zero, R.coefficient_zero] using
      congrArg (fun f ↦ f ≫ (J.iCycles p).f 0) h₀
  · calc
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.toCycles (p - 1) p) ≫
          y ≫ J.iCycles p =
          (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (factorThruImage (I.d (p - 1) p)) ≫ R.i ≫ y ≫ J.iCycles p := by
        rw [← R.source_factor, Category.assoc]
      _ = (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (factorThruImage (I.d (p - 1) p)) ≫ b ≫ R.α ≫ J.iCycles p := by
        rw [← Category.assoc R.i y, hby, Category.assoc]
      _ = (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (factorThruImage (I.d (p - 1) p)) ≫ b ≫
              image.ι (J.d (p - 1) p) := by rw [R.target_inclusion]

end CategoryTheory
