/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Order.WithBotTop

/-!
# The smart vertical truncation tower before taking cones

Source: blueprint thm-sp-double-complex-spectral-sequences, construction in step 1;
Stacks, Homology, Section 12.25 (tag 012X), and canonical smart truncations.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Extension by zero followed by restriction in the vertical direction. -/
noncomputable def verticalReextension : CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙
    ComplexShape.embeddingUpNat.restrictionFunctor C

instance verticalReextension_preservesZero :
    (verticalReextension (C := C)).PreservesZeroMorphisms := by
  unfold verticalReextension
  infer_instance

/-- The columnwise smart truncation below the integer `b`. -/
noncomputable def verticalCutoff (b : ℤ) : CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙
    (ComplexShape.embeddingUpIntLE (b - 1)).truncLEFunctor C ⋙
    ComplexShape.embeddingUpNat.restrictionFunctor C

instance verticalCutoff_preservesZero (b : ℤ) :
    (verticalCutoff (C := C) b).PreservesZeroMorphisms := by
  unfold verticalCutoff
  infer_instance

/-- The inclusion of the smart cutoff into the reextended column. -/
noncomputable def verticalCutoffι (b : ℤ) :
    verticalCutoff (C := C) b ⟶ verticalReextension :=
  Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.whiskerRight
      ((ComplexShape.embeddingUpIntLE (b - 1)).ιTruncLENatTrans C)
      (ComplexShape.embeddingUpNat.restrictionFunctor C))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma extend_map_mono {K L : CochainComplex C ℕ} (f : K ⟶ L) [∀ n, Mono (f.f n)] :
    Mono (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    rw [HomologicalComplex.extendMap_f _ _ hn]
    infer_instance
  · exact (K.isZero_extend_X ComplexShape.embeddingUpNat i (by simpa using hi)).mono _
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cutoffMap (L : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b) :
    L.truncLE (a - 1) ⟶ L.truncLE (b - 1) := by
  have : (L.truncLE (a - 1)).IsStrictlyLE (b - 1) :=
    CochainComplex.isStrictlyLE_of_le _ (a - 1) (b - 1) (by omega)
  exact inv ((L.truncLE (a - 1)).ιTruncLE (b - 1)) ≫
    CochainComplex.truncLEMap (L.ιTruncLE (a - 1)) (b - 1)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma cutoffMap_ι (L : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b) :
    cutoffMap L a b hab ≫ L.ιTruncLE (b - 1) = L.ιTruncLE (a - 1) := by
  have : (L.truncLE (a - 1)).IsStrictlyLE (b - 1) :=
    CochainComplex.isStrictlyLE_of_le _ (a - 1) (b - 1) (by omega)
  simp [cutoffMap, Category.assoc, CochainComplex.ιTruncLE_naturality]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cutoffNatTrans (a b : ℤ) (hab : a ≤ b) :
    (ComplexShape.embeddingUpIntLE (a - 1)).truncLEFunctor C ⟶
      (ComplexShape.embeddingUpIntLE (b - 1)).truncLEFunctor C where
  app L := cutoffMap L a b hab
  naturality L M f := by
    change CochainComplex.truncLEMap f (a - 1) ≫ cutoffMap M a b hab =
      cutoffMap L a b hab ≫ CochainComplex.truncLEMap f (b - 1)
    have : Mono (CochainComplex.ιTruncLE M (b - 1)) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE M
        (ComplexShape.embeddingUpIntLE (b - 1))))
    apply (cancel_mono (CochainComplex.ιTruncLE M (b - 1))).1
    simp only [Category.assoc, cutoffMap_ι, CochainComplex.ιTruncLE_naturality]
    rw [← Category.assoc, cutoffMap_ι]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def verticalCutoffMap (a b : ℤ) (hab : a ≤ b) :
    verticalCutoff (C := C) a ⟶ verticalCutoff b :=
  Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.whiskerRight (cutoffNatTrans a b hab)
      (ComplexShape.embeddingUpNat.restrictionFunctor C))
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma verticalCutoffMap_ι (a b : ℤ) (hab : a ≤ b) :
    verticalCutoffMap (C := C) a b hab ≫ verticalCutoffι b = verticalCutoffι a := by
  apply NatTrans.ext
  funext L
  change HomologicalComplex.restrictionMap
    (cutoffMap (L.extend ComplexShape.embeddingUpNat) a b hab) ComplexShape.embeddingUpNat ≫
      HomologicalComplex.restrictionMap
        (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (b - 1))
        ComplexShape.embeddingUpNat =
      HomologicalComplex.restrictionMap
        (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (a - 1))
        ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.restrictionMap_comp, cutoffMap_ι]

variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
  L.HasTotal (ComplexShape.up ℕ)]
  (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The reextended total complex, now indexed by the integers. -/
noncomputable def verticalTowerTop : CochainComplex C ℤ :=
  (total (((verticalReextension (C := C)).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
    (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat

/-- The objects of the vertical smart truncation tower, including its two endpoints. -/
noncomputable def verticalTowerTerm : EInt → CochainComplex C ℤ :=
  WithBotTop.rec 0
    (fun b ↦ (total (((verticalCutoff b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
      (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat)
    (verticalTowerTop K)

/-- The canonical inclusions of the tower terms into its top. -/
noncomputable def verticalTowerι : ∀ i : EInt, verticalTowerTerm K i ⟶ verticalTowerTop K :=
  WithBotTop.rec 0
    (fun b ↦ HomologicalComplex.extendMap
      (total.map (((verticalCutoffι b).mapHomologicalComplex (ComplexShape.up ℕ)).app K)
        (ComplexShape.up ℕ)) ComplexShape.embeddingUpNat)
    (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma total_map_mono {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : K ⟶ L) [∀ p q, Mono ((f.f p).f q)] : Mono (total.map f (ComplexShape.up ℕ)) := by
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let π := ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
  have : Finite {i : ℕ × ℕ // π i = n} := by
    refine Set.Finite.to_subtype ((Set.finite_Iic (n, n)).subset ?_)
    rintro ⟨p, q⟩ (h : p + q = n)
    simp only [Set.mem_Iic, Prod.mk_le_mk]
    omega
  change Mono (GradedObject.mapMap (toGradedObjectMap f) π n)
  change Mono (CategoryTheory.Limits.Sigma.map
    (fun (i : {i : ℕ × ℕ // π i = n}) ↦ (f.f i.val.1).f i.val.2))
  have hi (i : {i : ℕ × ℕ // π i = n}) : Mono ((f.f i.val.1).f i.val.2) :=
    inferInstance
  have hk : HasBiproduct (fun (i : {i : ℕ × ℕ // π i = n}) ↦ (K.X i.val.1).X i.val.2) :=
    inferInstance
  have hl : HasBiproduct (fun (i : {i : ℕ × ℕ // π i = n}) ↦ (L.X i.val.1).X i.val.2) :=
    inferInstance
  exact CategoryTheory.Limits.Sigma.map_mono _
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma towerFiniteMono (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (b : ℤ) : Mono (verticalTowerι K (b : EInt)) := by
  let g := ((verticalCutoffι (C := C) b).mapHomologicalComplex (ComplexShape.up ℕ)).app K
  have hm (p q : ℕ) : Mono ((g.f p).f q) := by
    change Mono ((HomologicalComplex.ιTruncLE
      ((K.X p).extend ComplexShape.embeddingUpNat)
      (ComplexShape.embeddingUpIntLE (b - 1))).f (ComplexShape.embeddingUpNat.f q))
    infer_instance
  have : Mono (total.map g (ComplexShape.up ℕ)) := total_map_mono g
  have ht (n : ℕ) : Mono ((total.map g (ComplexShape.up ℕ)).f n) := inferInstance
  exact extend_map_mono _
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma towerFiniteFactor (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (a b : ℤ) (hab : a ≤ b) :
    ∃ f : verticalTowerTerm K (a : EInt) ⟶ verticalTowerTerm K (b : EInt),
      f ≫ verticalTowerι K b = verticalTowerι K a := by
  let α := verticalCutoffMap (C := C) a b hab
  let f := HomologicalComplex.extendMap
    (total.map ((α.mapHomologicalComplex (ComplexShape.up ℕ)).app K)
      (ComplexShape.up ℕ)) ComplexShape.embeddingUpNat
  refine ⟨f, ?_⟩
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ = _
  rw [← HomologicalComplex.extendMap_comp, ← total.map_comp]
  have h := congrArg (fun η ↦ (η.mapHomologicalComplex (ComplexShape.up ℕ)).app K)
    (verticalCutoffMap_ι (C := C) a b hab)
  simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at h
  rw [h]
  rfl

/-- The cutoff inclusions are monomorphisms and nested.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 1, canonical
smart truncations; Stacks tag 012X, filtration construction.
(blueprint: lem-sp-double-complex-vertical-tower-maps).

Proof: each smart cutoff inclusion is degreewise a kernel inclusion in its boundary
vertical degree, an identity below it, and the unique map from zero above it. Restriction
and extension by zero preserve these monomorphisms. In each total degree there are only
finitely many summands; finite biproducts in an abelian category preserve monomorphisms.
For i <= j, the inclusion of the i-cutoff factors through the j-cutoff: below the
j-boundary use the original inclusion, at that boundary use the kernel lift (the
vertical differential vanishes), and above it use the zero map. Kernel uniqueness
shows these maps commute with horizontal and vertical differentials. Totalize and
extend. At bottom take the zero map, at top the inclusion, and for a top-to-top arrow
use the identity. Monicity makes each factor unique. -/
theorem verticalTower_inclusion_mono_and_factors (i : EInt) :
    Mono (verticalTowerι K i) ∧
      ∀ (j : EInt) (_ : i ≤ j),
        ∃ f : verticalTowerTerm K i ⟶ verticalTowerTerm K j,
          f ≫ verticalTowerι K j = verticalTowerι K i := by
  constructor
  · induction i using WithBotTop.rec with
    | bot =>
      change Mono (0 : (0 : CochainComplex C ℤ) ⟶ verticalTowerTop K)
      infer_instance
    | coe b => exact towerFiniteMono K b
    | top =>
      change Mono (𝟙 (verticalTowerTop K))
      infer_instance
  · intro j hij
    induction i using WithBotTop.rec with
    | bot =>
      refine ⟨0, ?_⟩
      change 0 ≫ verticalTowerι K j = 0
      simp
    | coe a =>
      induction j using WithBotTop.rec with
      | bot => exact (not_le_of_gt (show (⊥ : EInt) < a from bot_lt_iff_ne_bot.mpr
          (WithBotTop.coe_ne_bot a)) hij).elim
      | coe b => exact towerFiniteFactor K a b (WithBotTop.coe_le_coe.mp hij)
      | top =>
        refine ⟨verticalTowerι K a, ?_⟩
        change verticalTowerι K a ≫ 𝟙 _ = verticalTowerι K a
        simp
    | top =>
      obtain rfl := top_le_iff.mp hij
      exact ⟨𝟙 _, by simp⟩

/-- The canonical map between two nested cutoff totals; uniqueness follows from monicity. -/
noncomputable def verticalTowerMap {i j : EInt} (h : i ≤ j) :
    verticalTowerTerm K i ⟶ verticalTowerTerm K j :=
  ((verticalTower_inclusion_mono_and_factors K i).2 j h).choose

@[reassoc (attr := simp)]
theorem verticalTowerMap_ι {i j : EInt} (h : i ≤ j) :
    verticalTowerMap K h ≫ verticalTowerι K j = verticalTowerι K i :=
  ((verticalTower_inclusion_mono_and_factors K i).2 j h).choose_spec

/-- The actual filtered complex whose intervals will be formed by mapping cones. -/
noncomputable def verticalTower : EInt ⥤ CochainComplex C ℤ where
  obj := verticalTowerTerm K
  map f := verticalTowerMap K (leOfHom f)
  map_id i := by
    have := (verticalTower_inclusion_mono_and_factors K i).1
    apply (cancel_mono (verticalTowerι K i)).1
    simp
  map_comp {i j k} f g := by
    have := (verticalTower_inclusion_mono_and_factors K k).1
    apply (cancel_mono (verticalTowerι K k)).1
    simp

end HomologicalComplex₂
