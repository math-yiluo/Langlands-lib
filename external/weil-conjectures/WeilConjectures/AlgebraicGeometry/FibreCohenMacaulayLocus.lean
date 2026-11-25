/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.AffineFibreCohenMacaulayLocus

/-! # Openness of the fibre Cohen-Macaulay locus

Source: Stacks Project, Tag 045U (1), (2).
(blueprint: lem-sbc-fibre-cohen-macaulay-locus-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem maximal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (IsLocalRing.maximalIdeal A).map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top

private theorem depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  simp only [IsLocalRing.depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A = IsLocalRing.depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_locus_source_iff
    {U X T : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : X ⟶ T) (x : U) :
    ((IsLocalRing.depth (R := ((i ≫ f).fiber ((i ≫ f) x)).presheaf.stalk
        ((i ≫ f).asFiber x))
      (((i ≫ f).fiber ((i ≫ f) x)).presheaf.stalk ((i ≫ f).asFiber x)) : WithBot ℕ∞) =
        ringKrullDim (((i ≫ f).fiber ((i ≫ f) x)).presheaf.stalk ((i ≫ f).asFiber x))) ↔
    ((IsLocalRing.depth (R := (f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x)))
      ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x))) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x)))) := by
  let q : (i ≫ f).fiber ((i ≫ f) x) ⟶ f.fiber (f (i x)) :=
    Limits.pullback.map (i ≫ f) (T.fromSpecResidueField (f (i x))) f
    (T.fromSpecResidueField (f (i x))) i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion q :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl (by simp)
  have hpoint : q ((i ≫ f).asFiber x) = f.asFiber (i x) := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q ≫ f.fiberι _ = (i ≫ f).fiberι _ ≫ i := by
      simp [q, Scheme.Hom.fiberι]
    have hh := congrArg
      (fun g : (i ≫ f).fiber ((i ≫ f) x) ⟶ X ↦ g ((i ≫ f).asFiber x)) hfst
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using hh
  let e := ((f.fiber (f (i x))).presheaf.stalkCongr (.of_eq hpoint.symm) ≪≫
    asIso (q.stalkMap ((i ≫ f).asFiber x))).commRingCatIsoToRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e, ← depth_eq_of_ringEquiv e]

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_locus_base_iff
    {X T V : Scheme.{u}} (f : X ⟶ T) (i : V ⟶ T) [IsOpenImmersion i]
    (x : ↥(Limits.pullback f i)) :
    ((IsLocalRing.depth
        (R := ((Limits.pullback.snd f i).fiber ((Limits.pullback.snd f i) x)).presheaf.stalk
          ((Limits.pullback.snd f i).asFiber x))
        (((Limits.pullback.snd f i).fiber ((Limits.pullback.snd f i) x)).presheaf.stalk
          ((Limits.pullback.snd f i).asFiber x)) : WithBot ℕ∞) =
      ringKrullDim
        (((Limits.pullback.snd f i).fiber ((Limits.pullback.snd f i) x)).presheaf.stalk
          ((Limits.pullback.snd f i).asFiber x))) ↔
    ((IsLocalRing.depth
        (R := (f.fiber (f ((Limits.pullback.fst f i) x))).presheaf.stalk
          (f.asFiber ((Limits.pullback.fst f i) x)))
        ((f.fiber (f ((Limits.pullback.fst f i) x))).presheaf.stalk
          (f.asFiber ((Limits.pullback.fst f i) x))) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber (f ((Limits.pullback.fst f i) x))).presheaf.stalk
        (f.asFiber ((Limits.pullback.fst f i) x)))) := by
  let v := (Limits.pullback.snd f i) x
  let q := Limits.pullback.map (Limits.pullback.snd f i) (V.fromSpecResidueField v) f
    (T.fromSpecResidueField (i v)) (Limits.pullback.fst f i)
    (Spec.map (i.residueFieldMap v)) i Limits.pullback.condition.symm
    (by exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField i v).symm)
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f i) v
  have : IsIso q := hsq.isIso_fst_of_isIso
  have hbase : i v = f ((Limits.pullback.fst f i) x) := by
    exact congrArg (fun g : Limits.pullback f i ⟶ T ↦ g x) Limits.pullback.condition.symm
  let q' : (Limits.pullback.snd f i).fiber v ⟶
      f.fiber (f ((Limits.pullback.fst f i) x)) :=
    q ≫ eqToHom (congrArg f.fiber hbase)
  have : IsIso q' := inferInstance
  have hpoint : q' ((Limits.pullback.snd f i).asFiber x) =
      f.asFiber ((Limits.pullback.fst f i) x) := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q' ≫ f.fiberι (f ((Limits.pullback.fst f i) x)) =
        (Limits.pullback.snd f i).fiberι v ≫ Limits.pullback.fst f i := by
      dsimp [q']
      have heq (t t' : T) (h : t = t') :
          eqToHom (congrArg f.fiber h) ≫ f.fiberι t' = f.fiberι t := by
        subst t'
        simp
      rw [Category.assoc, heq _ _ hbase]
      simp [q, Scheme.Hom.fiberι]
    rw [← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply]
    simp only [v, Scheme.Hom.fiberι_asFiber]
  let e := ((f.fiber (f ((Limits.pullback.fst f i) x))).presheaf.stalkCongr
      (.of_eq hpoint.symm) ≪≫
    asIso (q'.stalkMap ((Limits.pullback.snd f i).asFiber x))).commRingCatIsoToRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e, ← depth_eq_of_ringEquiv e]

private theorem isOpen_of_openCover_preimage {X : Scheme.{u}}
    (C : X.OpenCover) (s : Set X) (h : ∀ j, IsOpen ((C.f j) ⁻¹' s)) : IsOpen s := by
  have hs : s = ⋃ j, (C.f j) '' ((C.f j) ⁻¹' s) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := C.covers x
      exact ⟨C.idx x, y, by simpa only [hy] using hx, hy⟩
    · rintro ⟨j, y, hy, rfl⟩
      exact hy
  rw [hs]
  exact isOpen_iUnion fun j ↦ (C.f j).isOpenEmbedding.isOpenMap _ (h j)

private theorem isOpen_fibre_locus_of_affine_base
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {y : X |
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by
  apply isOpen_of_openCover_preimage X.affineCover
  intro j
  convert isOpen_fibre_depth_eq_ringKrullDim_of_isAffine (X.affineCover.f j ≫ f) using 1
  ext x
  exact (fibre_locus_source_iff (X.affineCover.f j) f x).symm

/-- The fibre-stalk depth-equals-dimension locus of a flat locally finitely presented
morphism is open.

Source: Stacks Project, Tag 045U (1), (2), and Tag 00N8.
Proof: Cover the base and source by affine opens. On each affine chart the morphism
is given by a flat finitely presented algebra. Algebra, Tag 00RI gives openness of
its fibre Cohen-Macaulay locus. Fibres are locally of finite type over residue
fields and therefore locally Noetherian. In a Noetherian local ring, being
Cohen-Macaulay as a module over itself means that its depth equals its dimension;
the regular-sequence definition of depth and ring Krull dimension used here give
exactly this condition. The chartwise open sets agree on overlaps, since both
conditions depend only on the fibre local ring, and their union is the displayed
locus. An empty source has empty locus, so requires no exception.
(blueprint: lem-sbc-fibre-cohen-macaulay-locus-open) -/
theorem isOpen_fibre_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {y : X |
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by
  apply isOpen_of_openCover_preimage (T.affineCover.pullback₁ f)
  intro j
  have : Flat (T.affineCover.pullbackHom f j) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFinitePresentation (T.affineCover.pullbackHom f j) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  convert isOpen_fibre_locus_of_affine_base (T.affineCover.pullbackHom f j) using 1
  ext x
  exact (fibre_locus_base_iff f (T.affineCover.f j) x).symm

end AlgebraicGeometry
