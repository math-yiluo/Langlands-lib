/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Complements on morphisms locally of finite type

We show that the sections over an affine open of a scheme locally of finite type over `Spec ℤ`
form a finitely generated `ℤ`-algebra
(`AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType`), and that for a
morphism of finite type between affine schemes the global sections of the source are generated
by the image of the global sections of the target together with finitely many elements
(`AlgebraicGeometry.exists_finset_closure_range_appTop_union_eq_top`). An integral scheme locally
of finite type over a field has the dimension of any of its nonempty open subschemes
(`AlgebraicGeometry.topologicalKrullDim_opens_eq`), since all its nonempty affine opens have
the same dimension (`AlgebraicGeometry.IsAffineOpen.topologicalKrullDim_eq_of_isIntegral`); this
dimension is finite (`AlgebraicGeometry.topologicalKrullDim_ne_top`). More generally, a
quasi-compact scheme locally of finite type over a field has finite dimension
(`AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace`).

A `Y`-scheme `X ⟶ Y` is the colimit of its restrictions `X ×_Y U` to the affine opens `U` of `Y`
(`AlgebraicGeometry.Scheme.Over.nonempty_iso_of_restrictAffineOpens_iso`). If `X ⟶ Y` is affine
and locally of finite type, these restrictions are affine schemes locally of finite type over
`Y`, which form an essentially small category
(`AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec`). Hence the `Y`-schemes affine and
locally of finite type over `Y` form an essentially small family
(`AlgebraicGeometry.Scheme.Over.small_skeleton_isAffineHomLocallyOfFiniteType`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The sections over an affine open of a scheme of finite type over `Spec ℤ` form a
finitely generated `ℤ`-algebra. -/
theorem IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))} [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  rw [← RingHom.finiteType_algebraMap,
    Subsingleton.elim (algebraMap ℤ Γ(X, U))
      (((f.appLE ⊤ U (by simp)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)]
  refine (hft.comp (RingHom.FiniteType.of_surjective _ ?_)).comp
    (RingHom.FiniteType.of_surjective _ (ULift.ringEquiv (R := ℤ)).symm.surjective)
  exact (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).symm.commRingCatIsoToRingEquiv.surjective

/-- If `f : X ⟶ Y` is a morphism of finite type between affine schemes, then `Γ(X, ⊤)` is
generated as a ring by the image of `Γ(Y, ⊤)` together with finitely many elements. -/
lemma exists_finset_closure_range_appTop_union_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [LocallyOfFiniteType f] :
    ∃ s : Finset Γ(X, ⊤),
      Subring.closure (Set.range ⇑f.appTop.hom ∪ (s : Set Γ(X, ⊤))) = ⊤ := by
  have hft : RingHom.FiniteType f.appTop.hom :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType).mp inferInstance
  let := f.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, ?_⟩
  have h2 : (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = f.appTop.hom := RingHom.algebraMap_toAlgebra _
  have h3 := Algebra.adjoin_eq_ring_closure (R := Γ(Y, ⊤)) (A := Γ(X, ⊤)) (s : Set Γ(X, ⊤))
  rw [hs] at h3
  rw [← h2, ← h3]
  rfl

/-- The dimension of an affine open subscheme is the Krull dimension of its ring of sections. -/
theorem IsAffineOpen.topologicalKrullDim_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := by
  have := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (U : Set X) = topologicalKrullDim (PrimeSpectrum Γ(X, U)) at this
  rw [this, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]

/-- The sections over an affine open of a scheme locally of finite type over a field `K` form a
finitely generated `K`-algebra. -/
theorem IsAffineOpen.algebra_finiteType_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    Algebra.FiniteType K Γ(X, U) := by
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  exact hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)

/-- In an integral scheme locally of finite type over a field, an affine open subscheme `V` has
the same dimension as each nonempty basic open `D(a) ⊆ V`: `Γ(X, D(a))` is the localization of
the finitely generated domain `Γ(X, V)` away from `a ≠ 0`. -/
theorem IsAffineOpen.topologicalKrullDim_basicOpen {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] {V : X.Opens}
    (hV : IsAffineOpen V) (a : Γ(X, V)) (h : (X.basicOpen a : Set X).Nonempty) :
    topologicalKrullDim (X.basicOpen a : Set X) = topologicalKrullDim (V : Set X) := by
  obtain ⟨x, hx⟩ := h
  have : Nonempty V := ⟨⟨x, X.basicOpen_le a hx⟩⟩
  let := ((f.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have := hV.algebra_finiteType_of_field f
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have := hV.isLocalization_basicOpen a
  rw [hV.topologicalKrullDim_eq, (hV.basicOpen a).topologicalKrullDim_eq,
    ringKrullDim_eq_of_isLocalization_away (K := K) ha]

/-- In an integral scheme locally of finite type over a field, all nonempty affine open
subschemes have the same dimension: any two of them meet, and their intersection contains a
nonempty open which is a basic open of both. -/
theorem IsAffineOpen.topologicalKrullDim_eq_of_isIntegral {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X]
    {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hV' : (V : Set X).Nonempty)
    (hW' : (W : Set X).Nonempty) :
    topologicalKrullDim (V : Set X) = topologicalKrullDim (W : Set X) := by
  obtain ⟨x, hxV, hxW⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen hV' hW'
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter hV hW x ⟨hxV, hxW⟩
  rw [← hV.topologicalKrullDim_basicOpen f a ⟨x, hxa⟩, hab,
    hW.topologicalKrullDim_basicOpen f b ⟨x, hab ▸ hxa⟩]

/-- An integral scheme `X` locally of finite type over a field `K` has the same dimension as each
of its nonempty open subschemes: all nonempty affine opens of `X` have the same dimension
(`AlgebraicGeometry.IsAffineOpen.topologicalKrullDim_eq_of_isIntegral`), and they cover both
`X` and `U`. -/
theorem topologicalKrullDim_opens_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] (U : X.Opens) [Nonempty U] :
    topologicalKrullDim (U : Set X) = topologicalKrullDim X := by
  obtain ⟨⟨x, hxU⟩⟩ := ‹Nonempty U›
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  refine le_antisymm (topologicalKrullDim_subspace_le X U) ?_
  calc topologicalKrullDim X ≤ topologicalKrullDim (V : Set X) := by
        refine topologicalKrullDim_le_of_iSup_eq_top
          (fun W : {W : X.affineOpens // (W.1 : Set X).Nonempty} ↦ W.1.1) ?_ _ fun W ↦
            (W.1.2.topologicalKrullDim_eq_of_isIntegral f hV W.2 ⟨x, hxV⟩).le
        refine eq_top_iff.mpr fun y _ ↦ ?_
        obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, ⟨y, hyW⟩⟩, hyW⟩
    _ ≤ topologicalKrullDim (U : Set X) :=
        have : QuasiSober (V : Set X) := V.isOpenEmbedding'.quasiSober
        have : QuasiSober (U : Set X) := U.isOpenEmbedding'.quasiSober
        topologicalKrullDim_le_of_continuous (continuous_inclusion hVU)
          fun _ _ _ h ↦ Set.inclusion_injective hVU h

/-- An affine open subscheme of a scheme locally of finite type over a field `K` has finite
dimension: it is the spectrum of a finitely generated `K`-algebra. -/
theorem IsAffineOpen.topologicalKrullDim_ne_top {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) ≠ ⊤ := by
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  let φ : K →+* Γ(X, U) := (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  let := φ.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hφ
  have := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (U : Set X) = topologicalKrullDim (PrimeSpectrum Γ(X, U)) at this
  rw [this, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_ne_top_of_finiteType K _

/-- An integral scheme locally of finite type over a field has finite dimension: the dimension of
any nonempty affine open subscheme, the spectrum of a finitely generated algebra. -/
theorem topologicalKrullDim_ne_top {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] :
    topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [← topologicalKrullDim_opens_eq f U]
  exact hU.topologicalKrullDim_ne_top f

/-- A quasi-compact scheme locally of finite type over a field has finite dimension: it is
covered by finitely many affine open subschemes, each of finite dimension. -/
theorem topologicalKrullDim_ne_top_of_compactSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [CompactSpace X] :
    topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  refine (lt_of_le_of_lt (topologicalKrullDim_le_of_iSup_eq_top (fun U : t ↦ U.1.1) ?_
    (t.sup fun U ↦ topologicalKrullDim U.1) fun U ↦
      Finset.le_sup (f := fun V : X.affineOpens ↦ topologicalKrullDim V.1) U.2) ?_).ne
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · exact (Finset.sup_lt_iff bot_lt_top).mpr fun U _ ↦
      (U.2.topologicalKrullDim_ne_top f).lt_top

/-- A scheme which is quasi-compact and locally of finite type over a field has finite
dimension. -/
lemma exists_topologicalKrullDim_le {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have h := topologicalKrullDim_ne_top_of_compactSpace f
  generalize topologicalKrullDim X = n at h
  induction n using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd rfl h
    | coe n => exact ⟨n, le_rfl⟩

/-- A scheme with a morphism locally of finite type over `S` to a scheme locally of finite type
over `S` is locally of finite type over `S`. -/
lemma locallyOfFiniteType_over_of_isOver {X Y S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y)
    [f.IsOver S] [LocallyOfFiniteType f] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (X ↘ S) := by
  rw [← CategoryTheory.comp_over f S]
  infer_instance

end AlgebraicGeometry

open Limits

namespace AlgebraicGeometry.Scheme.Over

variable {Y : Scheme.{u}}

/-- The restrictions `X ×_Y U ⟶ Y` of a `Y`-scheme `X` to the affine opens `U` of `Y`, as a
diagram of `Y`-schemes indexed by the affine opens. -/
noncomputable def restrictAffineOpens (X : Over Y) : Y.affineOpens ⥤ Over Y :=
  (Cover.functorOfLocallyDirected (Y.directedAffineCover.pullback₁ X.hom)).toOver Y
    (fun U ↦ (Y.directedAffineCover.pullback₁ X.hom).f U ≫ X.hom) fun g ↦ by
      rw [Cover.functorOfLocallyDirected_map, ← Category.assoc, Cover.trans_map]

/-- A `Y`-scheme is determined up to isomorphism by its restrictions to the affine opens of
`Y`. -/
theorem nonempty_iso_of_restrictAffineOpens_iso {X X' : Over Y}
    (e : restrictAffineOpens X ≅ restrictAffineOpens X') : Nonempty (X ≅ X') := by
  let 𝒰 := Y.directedAffineCover.pullback₁ X.hom
  let 𝒰' := Y.directedAffineCover.pullback₁ X'.hom
  let e' : Cover.functorOfLocallyDirected 𝒰 ≅ Cover.functorOfLocallyDirected 𝒰' :=
    Functor.isoWhiskerRight e (Over.forget Y)
  let φ : X.left ≅ X'.left := IsColimit.coconePointsIsoOfNatIso
    (OpenCover.isColimitCoconeOfLocallyDirected 𝒰)
    (OpenCover.isColimitCoconeOfLocallyDirected 𝒰') e'
  refine ⟨Over.isoMk φ ?_⟩
  refine Cover.hom_ext 𝒰 _ _ fun U ↦ ?_
  have h₁ : 𝒰.f U ≫ φ.hom = e'.hom.app U ≫ 𝒰'.f U :=
    IsColimit.comp_coconePointsIsoOfNatIso_hom (OpenCover.isColimitCoconeOfLocallyDirected 𝒰)
      (OpenCover.isColimitCoconeOfLocallyDirected 𝒰') e' U
  have h₂ := Over.w (e.hom.app U)
  rw [← Category.assoc, h₁, Category.assoc]
  exact h₂

/-- The `Y`-schemes which are affine and locally of finite type over `Y`. -/
def isAffineHomLocallyOfFiniteType : ObjectProperty (Over Y) :=
  fun X ↦ IsAffineHom X.hom ∧ LocallyOfFiniteType X.hom

/-- The `Y`-schemes whose source is affine and which are locally of finite type over `Y`. -/
def isAffineLocallyOfFiniteType : ObjectProperty (Over Y) :=
  fun X ↦ IsAffine X.left ∧ LocallyOfFiniteType X.hom

instance : ObjectProperty.EssentiallySmall.{u} (isAffineLocallyOfFiniteType (Y := Y)) := by
  have := essentiallySmall_costructuredArrow_Spec (X := Y) @LocallyOfFiniteType le_rfl
  let F := MorphismProperty.CostructuredArrow.forget @LocallyOfFiniteType ⊤ Scheme.Spec Y ⋙
    CostructuredArrow.toOver Scheme.Spec Y
  refine ObjectProperty.EssentiallySmall.of_le (Q := F.essImage) fun X ⟨hX, hf⟩ ↦ ?_
  refine ⟨MorphismProperty.CostructuredArrow.mk ⊤ (A := Opposite.op Γ(X.left, ⊤))
    (X.left.isoSpec.inv ≫ X.hom)
      ((MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType _ _).2 hf),
    ⟨Over.isoMk X.left.isoSpec.symm⟩⟩

instance : LocallySmall.{u} (isAffineLocallyOfFiniteType (Y := Y)).FullSubcategory where
  hom_small _ _ := inferInstance

/-- The restriction of a `Y`-scheme affine and locally of finite type over `Y` to an affine open
of `Y` is affine and locally of finite type over `Y`. -/
lemma isAffineLocallyOfFiniteType_restrictAffineOpens_obj {X : Over Y}
    (hX : isAffineHomLocallyOfFiniteType X) (U : Y.affineOpens) :
    isAffineLocallyOfFiniteType ((restrictAffineOpens X).obj U) := by
  obtain ⟨_, _⟩ := hX
  have : IsAffine U.1.toScheme := U.2
  refine ⟨?_, ?_⟩
  · have : IsAffineHom (pullback.snd X.hom U.1.ι) :=
      MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ ‹_›
    exact isAffine_of_isAffineHom (pullback.snd X.hom U.1.ι)
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom U.1.ι ≫ X.hom))

/-- **`Y`-schemes affine and locally of finite type over `Y` form an essentially small
family.** -/
theorem small_skeleton_isAffineHomLocallyOfFiniteType :
    Small.{u} (Skeleton (isAffineHomLocallyOfFiniteType (Y := Y)).FullSubcategory) := by
  let D := (isAffineLocallyOfFiniteType (Y := Y)).FullSubcategory
  have : EssentiallySmall.{u} (Y.affineOpens ⥤ D) := by
    rw [essentiallySmall_congr ((equivSmallModel.{u} D).congrRight (E := Y.affineOpens))]
    exact EssentiallySmall.mk' (CategoryTheory.Equivalence.refl)
  let H (X : (isAffineHomLocallyOfFiniteType (Y := Y)).FullSubcategory) : Y.affineOpens ⥤ D :=
    ObjectProperty.lift _ (restrictAffineOpens X.obj)
      (isAffineLocallyOfFiniteType_restrictAffineOpens_obj X.property)
  let g : Skeleton (isAffineHomLocallyOfFiniteType (Y := Y)).FullSubcategory →
      Skeleton (Y.affineOpens ⥤ D) := fun x ↦ toSkeleton (H (Quotient.out x))
  refine small_of_injective (f := g) fun x y hxy ↦ ?_
  obtain ⟨e⟩ : Nonempty (H (Quotient.out x) ≅ H (Quotient.out y)) := Quotient.exact hxy
  obtain ⟨e'⟩ := nonempty_iso_of_restrictAffineOpens_iso
    (Functor.isoWhiskerRight e (ObjectProperty.ι _))
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  exact Quotient.sound ⟨ObjectProperty.isoMk _ e'⟩

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry

/-- An open subscheme of a scheme locally of finite type over `S` is locally of finite type over
`S`. -/
instance locallyOfFiniteType_opens_over {X S : Scheme.{u}} [X.Over S] [LocallyOfFiniteType (X ↘ S)]
    (U : X.Opens) : LocallyOfFiniteType (U.toScheme ↘ S) := by
  rw [← Scheme.Opens.ι_comp_over]
  infer_instance

end AlgebraicGeometry
