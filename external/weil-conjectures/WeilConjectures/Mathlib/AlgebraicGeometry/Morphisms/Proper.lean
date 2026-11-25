/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Finite products of proper schemes, and dense proper open subschemes

## Images of proper morphisms

The scheme-theoretic image of a proper morphism into a separated scheme of finite type is
proper (`AlgebraicGeometry.isProper_imageι_comp`), and a proper affine scheme over a field is
finite and of dimension zero (`AlgebraicGeometry.isFinite_of_isProper_of_isAffine`).

## Base change

Proper morphisms and smooth morphisms are stable under base change
(`AlgebraicGeometry.isProper_and_smooth_of_isPullback`).

## Finite products

A finite product of proper `S`-schemes is proper over `S`
(`AlgebraicGeometry.isProper_pi_hom`). This is an instance of the general fact that the
structure morphism of a finite product in an over category satisfies any multiplicative
morphism property that is stable under base change.

## Dense proper open subschemes

An open subscheme `V` of a scheme `Z` that is topologically dense in a larger open `W` and
whose inclusion into `W` is universally closed is all of `W`
(`AlgebraicGeometry.Scheme.Opens.eq_of_universallyClosed_of_dense`). Since properness of a
composite `V ⟶ W ⟶ T` with `W ⟶ T` separated forces the inclusion `V ⟶ W` to be
universally closed, this gives the form used in practice,
`AlgebraicGeometry.Scheme.Opens.eq_of_isProper_of_dense`, and its variant
`AlgebraicGeometry.Scheme.Opens.eq_of_isProper_of_isSchemeTheoreticallyDominant`, where the
density is supplied by a quasi-compact scheme-theoretically dense open contained in `V`.

## Immersions of proper schemes

An immersion `f` whose composite with a separated morphism `g` is universally closed is a closed
immersion (`AlgebraicGeometry.IsClosedImmersion.of_comp_of_isSeparated`); for instance, an
immersion of a proper `S`-scheme into a separated `S`-scheme is closed.

## Schemes with at most one point

A separated morphism locally of finite type from a scheme with at most one point to a Jacobson
scheme is proper (`AlgebraicGeometry.isProper_of_subsingleton`).

## Morphisms over a base

A morphism over `S` from a proper `S`-scheme to a separated `S`-scheme is proper
(`AlgebraicGeometry.isProper_left_of_isProper_of_isSeparated`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The structure morphism of a finite product of proper `S`-schemes is proper. -/
theorem isProper_pi_hom {S : Scheme.{u}} {ι : Type*} [Finite ι] (F : ι → Over S)
    [HasProduct F] [∀ i, IsProper (F i).hom] : IsProper (∏ᶜ F).hom :=
  MorphismProperty.pi_hom _ F fun _ ↦ inferInstance

/-- **Proper and smooth morphisms are stable under base change.** Let `f : X ⟶ S` be proper,
`g : S' ⟶ S` arbitrary and `f' : X' ⟶ S'` the base change of `f` along `g`. Then `f'` is proper,
and if `f` is smooth, then so is `f'`.

(blueprint: `lem-pc-proper-base-change`) -/
theorem isProper_and_smooth_of_isPullback {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (h : IsPullback g' f' f g) [IsProper f] :
    IsProper f' ∧ (Smooth f → Smooth f') :=
  ⟨IsProper.isStableUnderBaseChange.of_isPullback h ‹_›,
    fun hf ↦ smooth_isStableUnderBaseChange.of_isPullback h hf⟩

/-- An immersion `f : X ⟶ Y` whose composite with a separated morphism `g : Y ⟶ Z` is
universally closed is a closed immersion: `f` is then itself universally closed, so its image is
closed. In particular, an immersion of a proper `Z`-scheme into a separated `Z`-scheme is a
closed immersion. -/
theorem IsClosedImmersion.of_comp_of_isSeparated {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsImmersion f] [UniversallyClosed (f ≫ g)] [IsSeparated g] : IsClosedImmersion f :=
  have : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f g
  .of_isPreimmersion f f.isClosedMap.isClosed_range

/-- **The scheme-theoretic image of a proper morphism is proper.** Let `g : Y ⟶ S` be separated
and locally of finite type and let `f : X ⟶ Y` be such that `f ≫ g` is proper. Then the
scheme-theoretic image `f.image` of `f` is proper over `S`, and `f.toImage : X ⟶ f.image` is
proper and surjective. Universal closedness of `f.image ⟶ S` follows from that of `f ≫ g`,
since `f.toImage` is surjective. (blueprint: `pqf-lem-image-proper`) -/
theorem isProper_imageι_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsProper (f ≫ g)]
    [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper (f.imageι ≫ g) ∧ IsProper f.toImage ∧ Surjective f.toImage := by
  have : IsProper f := .of_comp f g
  have : IsProper (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : IsProper f.toImage := .of_comp f.toImage f.imageι
  have : UniversallyClosed (f.toImage ≫ f.imageι ≫ g) := by
    rw [← Category.assoc, f.toImage_imageι]; infer_instance
  have : UniversallyClosed (f.imageι ≫ g) := .of_comp_surjective f.toImage (f.imageι ≫ g)
  exact ⟨{ }, inferInstance, inferInstance⟩

/-- **Proper affine schemes over a field are finite.** If `X` is affine and proper over a field
`K`, then `X` is finite over `K`, so `Γ(X, 𝒪_X)` is an artinian ring and `X` has dimension
zero. (blueprint: `lem-sc-proper-affine-finite`) -/
theorem isFinite_of_isProper_of_isAffine {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [IsProper f] [IsAffine X] :
    IsFinite f ∧ topologicalKrullDim X ≤ 0 := by
  have : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨this, ?_⟩
  let φ : CommRingCat.of K ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  have : φ.hom.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  algebraize [φ.hom]
  have : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso X.isoSpec).symm.isHomeomorph]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, ⊤))).le.trans
    (Ring.krullDimLE_iff.mp inferInstance)

variable {Z T : Scheme.{u}}

/-- If `V ≤ W` are opens of a scheme `Z` such that the inclusion `V ⟶ W` is universally
closed and `V` is topologically dense in `W`, then `V = W`. -/
theorem Scheme.Opens.eq_of_universallyClosed_of_dense {V W : Z.Opens} (h : V ≤ W)
    [UniversallyClosed (Z.homOfLE h)] (hd : (W : Set Z) ⊆ closure (V : Set Z)) :
    V = W := by
  have hrange : Set.range (Z.homOfLE h).base = W.ι.base ⁻¹' (V : Set Z) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    rfl
  have hdr : DenseRange (Z.homOfLE h).base := by
    rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, hrange,
      ← W.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage W.ι.continuous]
    exact fun x _ ↦ hd x.2
  have : IsDominant (Z.homOfLE h) := ⟨hdr⟩
  refine le_antisymm h fun x hx ↦ ?_
  obtain ⟨y, hy⟩ := (Z.homOfLE h).surjective ⟨x, hx⟩
  have hx' : (⟨x, hx⟩ : W.toScheme) ∈ Set.range (Z.homOfLE h).base := ⟨y, hy⟩
  rw [hrange] at hx'
  exact hx'

/-- An open subscheme `V ≤ W` that is proper over a base `T` over which `W` is separated and
that is topologically dense in `W` is all of `W`. -/
theorem Scheme.Opens.eq_of_isProper_of_dense {V W : Z.Opens} (h : V ≤ W) (q : W.toScheme ⟶ T)
    [IsProper (Z.homOfLE h ≫ q)] [IsSeparated q]
    (hd : (W : Set Z) ⊆ closure (V : Set Z)) :
    V = W :=
  have : UniversallyClosed (Z.homOfLE h) :=
    UniversallyClosed.of_comp_of_isSeparated (f := Z.homOfLE h) (g := q)
  eq_of_universallyClosed_of_dense h hd

/-- An open subscheme `V ≤ W` that is proper over a base `T` over which `W` is separated and
that contains a quasi-compact scheme-theoretically dense open of `Z` is all of `W`. -/
theorem Scheme.Opens.eq_of_isProper_of_isSchemeTheoreticallyDominant {V W : Z.Opens} (h : V ≤ W)
    (q : W.toScheme ⟶ T) [IsProper (Z.homOfLE h ≫ q)] [IsSeparated q]
    (D : Z.Opens) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι] (hD : D ≤ V) :
    V = W :=
  eq_of_isProper_of_dense h q <| by
    have : closure (D : Set Z) = Set.univ := by
      simpa using D.ι.denseRange.closure_range
    exact fun x _ ↦ closure_mono hD (this ▸ Set.mem_univ x)

section Basic

/-! ### Basic properties of proper morphisms

These are the elementary facts about proper morphisms and closed immersions used in the curve
estimates; all of them are instances or direct consequences of results of Mathlib. -/

variable {X Y Z : Scheme.{u}}

/-- A closed immersion is proper, and so is a closed immersion followed by a proper morphism.
(blueprint: `lem-weil-pbc-closed-immersion-proper`) -/
theorem IsProper.of_isClosedImmersion (i : X ⟶ Y) [IsClosedImmersion i] : IsProper i :=
  inferInstance

/-- A closed immersion followed by a proper morphism is proper.
(blueprint: `lem-weil-pbc-closed-immersion-proper`) -/
theorem IsProper.isClosedImmersion_comp (i : X ⟶ Y) (f : Y ⟶ Z) [IsClosedImmersion i]
    [IsProper f] : IsProper (i ≫ f) :=
  inferInstance

/-- A proper morphism is a closed map.
(blueprint: `pqf-lem-proper-closed-map`) -/
theorem IsProper.isClosedMap (f : X ⟶ Y) [IsProper f] : IsClosedMap f :=
  f.isClosedMap

/-- The image of a proper morphism is closed.
(blueprint: `lem-weil-pbc-proper-closed-image`) -/
theorem IsProper.isClosed_range (f : X ⟶ Y) [IsProper f] : IsClosed (Set.range f) :=
  f.isClosedMap.isClosed_range

/-- If `f : X ⟶ Y` is proper and `g : X ⟶ W` is a morphism over `Y` to a separated `Y`-scheme,
then `g` is proper.
(blueprint: `lem-weil-pbc-proper-to-separated`) -/
theorem IsProper.of_comp_eq {W : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : X ⟶ W) (h : W ⟶ Y)
    [IsSeparated h] (hgh : g ≫ h = f) : IsProper g := by
  subst hgh
  exact IsProper.of_comp g h

/-- The composite of proper morphisms is proper.
(blueprint: `lem-weil-pbc-proper-composition`) -/
theorem IsProper.comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] : IsProper (f ≫ g) :=
  inferInstance

/-- Proper morphisms are stable under base change.
(blueprint: `lem-weil-pbc-proper-base-change`) -/
theorem IsProper.pullback_snd (f : X ⟶ Y) [IsProper f] {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsProper (pullback.snd f g) :=
  inferInstance

/-- The composite of closed immersions is a closed immersion.
(blueprint: `lem-weil-pbc-closed-immersion-products`) -/
theorem IsClosedImmersion.comp' (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion f]
    [IsClosedImmersion g] : IsClosedImmersion (f ≫ g) :=
  inferInstance

/-- A product over a common base of closed immersions is a closed immersion.
(blueprint: `lem-weil-pbc-closed-immersion-products`) -/
theorem IsClosedImmersion.pullback_map {S X' Y' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : X' ⟶ S} {g' : Y' ⟶ S} (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    IsClosedImmersion (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
      ((Category.comp_id _).trans e₂)) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance e₁ e₂

/-- An open immersion is locally of finite type.
(blueprint: `lem-weil-pbc-closed-immersion-products`) -/
theorem IsOpenImmersion.locallyOfFiniteType (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  inferInstance

end Basic

section Subsingleton

/-- A morphism of finite type from a scheme with at most one point to a Jacobson scheme
(e.g. the spectrum of a field) is proper. -/
lemma isProper_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y) [Subsingleton X]
    [LocallyOfFiniteType f] [IsSeparated f] [JacobsonSpace Y] : IsProper f := by
  cases isEmpty_or_nonempty X
  · have : IsClosedImmersion f := .of_isPreimmersion _ (by
      rw [Set.range_eq_empty]
      exact isClosed_empty)
    infer_instance
  obtain ⟨p⟩ := ‹Nonempty X›
  have : IsClosedImmersion (X.fromSpecResidueField p) := by
    rw [← isClosed_singleton_iff_isClosedImmersion, Set.Subsingleton.eq_singleton_of_mem
      (s := Set.univ) Set.subsingleton_of_subsingleton (Set.mem_univ p) |>.symm]
    exact isClosed_univ
  have : Surjective (X.fromSpecResidueField p) :=
    ⟨fun q ↦ ⟨default, (Subsingleton.elim _ _)⟩⟩
  have : IsFinite (X.fromSpecResidueField p ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have := UniversallyClosed.of_comp_surjective (X.fromSpecResidueField p) f
  exact ⟨⟩

end Subsingleton

/-- A morphism over `S` from a proper `S`-scheme to a separated `S`-scheme is proper. -/
lemma isProper_left_of_isProper_of_isSeparated {S : Scheme.{u}} {B Y : Over S} [IsProper B.hom]
    [IsSeparated Y.hom] (f : B ⟶ Y) : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact IsProper.of_comp _ Y.hom

end AlgebraicGeometry
