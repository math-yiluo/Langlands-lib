/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.IdentityComponent

/-!
# The image of a homomorphism of matrix groups is closed

Let `G = V(I) ⊆ GL_n` be a closed subgroup over an algebraically closed field `k` and let
`r : G ⟶ GL_m` be a homomorphism of group schemes (a `RationalHom`). The image `S = r(G(k))` is a
Zariski closed subgroup of `GL_m(k)`: it is the set of `k`-points of its Zariski closure.

The proof first treats the identity component: the image of `G°` is constructible with
irreducible closure `T`, so it contains a nonempty open subset `U` of `T`; translating `U` shows
that every `k`-point of `T` lies in `r(G°(k))`. Then `S` is the finite union of the translates of
`T` by the images of coset representatives of `G°(k)` in `G(k)`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.mem_range_points_iff`: the image of `G(k)` is
  the set of `k`-points of its Zariski closure.

## Blueprint

- `lemma-connected-components-images-homomorphisms--2`: the image of a regular homomorphism is
closed.
-/

@[expose] public section

universe u

open Topology CategoryTheory AlgebraicGeometry Matrix.GeneralLinearGroup
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {m : Type u} [Fintype m] [DecidableEq m]

namespace RationalHom

variable (r : RationalHom (subgroupScheme I) m)

/-- The coordinate map `k[GL_m] → k[GL_n] ⧸ I` of a homomorphism `r : V(I) ⟶ GL_m`. -/
noncomputable def coordMap : CoordinateRing m k →ₐ[k] CoordinateRing n k ⧸ I :=
  (Spec.mapMulEquiv.symm
    (show subgroupScheme I ⟶ (Spec (.of (CoordinateRing m k))).asOver (Spec (.of k)) from r)).ofConv

theorem mapMulEquiv_coordMap :
    (Spec.mapMulEquiv (WithConv.toConv r.coordMap) : subgroupScheme I ⟶ _) = r :=
  Spec.mapMulEquiv.apply_symm_apply _

variable [IsMonHom r]

/-- The homomorphism `r` on the `k`-points of `V(I)`, viewed as the matrix group `zeroLocus I k`. -/
noncomputable def zeroLocusPoints : zeroLocus I k →* GL m k :=
  (r.points k).comp (zeroLocusMulEquiv I k).toMonoidHom

theorem range_zeroLocusPoints : r.zeroLocusPoints.range = (r.points k).range := by
  ext x
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨_, hg⟩, fun ⟨p, hp⟩ ↦ ⟨(zeroLocusMulEquiv I k).symm p, ?_⟩⟩
  simp [zeroLocusPoints, hp]

/-- The point `r(g)` of `GL_m` is evaluation at `g` composed with the coordinate map of `r`. -/
theorem evalAlgHom_zeroLocusPoints (g : zeroLocus I k) :
    evalAlgHom (r.zeroLocusPoints g) =
      (Ideal.Quotient.liftₐ I (evalAlgHom (g : GL n k)) g.2).comp r.coordMap := by
  set χ := Ideal.Quotient.liftₐ I (evalAlgHom (g : GL n k)) g.2
  have hg : zeroLocusMulEquiv I k g = Spec.mapMulEquiv (WithConv.toConv χ) := by
    refine injective_homMulEquiv_comp I k ?_
    dsimp only
    rw [homMulEquiv_zeroLocusMulEquiv_comp, mapMulEquiv_comp_subgroupSchemeι,
      homMulEquiv_mapMulEquiv]
    refine (evalAlgHom_injective (k := k) ?_).symm
    dsimp only
    rw [algHomMulEquiv_apply, WithConv.ofConv_toConv, evalAlgHom_map_genericUnit]
    exact Ideal.Quotient.liftₐ_comp _ _ _
  have hr : Spec.mapMulEquiv (WithConv.toConv χ) ≫ r =
      (Spec.mapMulEquiv (WithConv.toConv (χ.comp r.coordMap)) :
        (Spec (.of k)).asOver (Spec (.of k)) ⟶ (Spec (.of (CoordinateRing m k))).asOver _) := by
    conv_lhs => rw [← r.mapMulEquiv_coordMap]
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  change evalAlgHom (homMulEquiv m k k (zeroLocusMulEquiv I k g ≫ r)) = _
  rw [hg, hr, homMulEquiv_mapMulEquiv, algHomMulEquiv_apply, WithConv.ofConv_toConv,
    evalAlgHom_map_genericUnit]

variable [IsAlgClosed k]

/-- The image `r(G°(k))` of the `k`-points of the identity component. -/
noncomputable def identityComponentImage : Subgroup (GL m k) :=
  ((zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)).map r.zeroLocusPoints

/-- The coordinate map `k[GL_m] → k[G°]` of the restriction of `r` to the identity component. -/
noncomputable def identityComponentCoordMap :
    CoordinateRing m k →ₐ[k] CoordinateRing n k ⧸ identityComponent I :=
  (Ideal.Quotient.factorₐ k (le_identityComponent I)).comp r.coordMap

/-- The image of `G°` in `Spec k[GL_m]`. -/
noncomputable def identityComponentRange : Set (PrimeSpectrum (CoordinateRing m k)) :=
  Set.range (PrimeSpectrum.comap (r.identityComponentCoordMap :
    CoordinateRing m k →+* CoordinateRing n k ⧸ identityComponent I))

theorem mem_identityComponentImage (g : GL n k) (hg : g ∈ zeroLocus (identityComponent I) k) :
    r.zeroLocusPoints ⟨g, zeroLocus_anti (le_identityComponent I) hg⟩ ∈ r.identityComponentImage :=
  Subgroup.mem_map_of_mem r.zeroLocusPoints (Subgroup.mem_subgroupOf.2 hg)

theorem comap_ker_liftₐ (g : GL n k) (hg : g ∈ zeroLocus (identityComponent I) k) :
    PrimeSpectrum.comap (r.identityComponentCoordMap :
        CoordinateRing m k →+* CoordinateRing n k ⧸ identityComponent I)
        ⟨RingHom.ker (Ideal.Quotient.liftₐ _ (evalAlgHom g) hg), RingHom.ker_isPrime _⟩ =
      toPrimeSpectrum (r.zeroLocusPoints ⟨g, zeroLocus_anti (le_identityComponent I) hg⟩) := by
  have key : evalAlgHom (r.zeroLocusPoints ⟨g, zeroLocus_anti (le_identityComponent I) hg⟩) =
      (Ideal.Quotient.liftₐ _ (evalAlgHom g) hg).comp r.identityComponentCoordMap := by
    rw [evalAlgHom_zeroLocusPoints, identityComponentCoordMap, ← AlgHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.algHom_ext k (AlgHom.ext fun a ↦ rfl)
  ext a
  simp only [toPrimeSpectrum, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker, key]
  rfl

/-- The `k`-points of the image of `G°` lie in `r(G°(k))`: the fibre over a closed point is a
nonempty finite type `k`-scheme, so it has a `k`-point. -/
theorem mem_identityComponentImage_of_mem_range {y : GL m k}
    (hy : toPrimeSpectrum y ∈ r.identityComponentRange) : y ∈ r.identityComponentImage := by
  obtain ⟨q, hq⟩ := hy
  obtain ⟨M, hM, hqM⟩ := q.asIdeal.exists_le_maximal q.2.ne_top
  obtain ⟨χ, hχM⟩ := exists_algHom_ker_eq_of_isMaximal k _ M
  obtain ⟨g, hg, rfl⟩ := exists_eq_liftₐ_evalAlgHom χ
  have hle : (toPrimeSpectrum y).asIdeal ≤ (toPrimeSpectrum
      (r.zeroLocusPoints ⟨g, zeroLocus_anti (le_identityComponent I) hg⟩)).asIdeal := by
    rw [← hq, ← r.comap_ker_liftₐ g hg]
    exact Ideal.comap_mono (hχM ▸ hqM)
  have hmax : (toPrimeSpectrum y).asIdeal.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap k _ c, by simp⟩
  rw [toPrimeSpectrum_injective (PrimeSpectrum.ext
    (hmax.eq_of_le (PrimeSpectrum.isPrime _).ne_top hle))]
  exact r.mem_identityComponentImage g hg

theorem image_identityComponentImage_subset_range :
    toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k)) ⊆ r.identityComponentRange := by
  rintro _ ⟨_, ⟨⟨g, hgI⟩, hg, rfl⟩, rfl⟩
  exact ⟨_, r.comap_ker_liftₐ g (Subgroup.mem_subgroupOf.1 hg)⟩

theorem range_subset_closure :
    r.identityComponentRange ⊆
      closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k))) := by
  have : IsJacobsonRing (CoordinateRing n k ⧸ identityComponent I) :=
    isJacobsonRing_of_finiteType (A := k)
  rintro _ ⟨q, rfl⟩
  have hq : q ∈ closure (closedPoints (PrimeSpectrum (CoordinateRing n k ⧸ identityComponent I))) :=
    by rw [closure_closedPoints]; trivial
  refine closure_mono ?_ (image_closure_subset_closure_image (PrimeSpectrum.continuous_comap _)
    ⟨q, hq, rfl⟩)
  rintro _ ⟨q, hq, rfl⟩
  have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 hq
  obtain ⟨χ, hχq⟩ := exists_algHom_ker_eq_of_isMaximal k _ q.asIdeal
  obtain ⟨g, hg, rfl⟩ := exists_eq_liftₐ_evalAlgHom χ
  obtain rfl : q = ⟨_, RingHom.ker_isPrime (Ideal.Quotient.liftₐ _ (evalAlgHom g) hg)⟩ :=
    PrimeSpectrum.ext hχq.symm
  rw [r.comap_ker_liftₐ g hg]
  exact ⟨_, r.mem_identityComponentImage g hg, rfl⟩

theorem closure_identityComponentRange :
    closure r.identityComponentRange =
      closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k))) :=
  (closure_minimal r.range_subset_closure isClosed_closure).antisymm
    (closure_mono r.image_identityComponentImage_subset_range)

omit [IsAlgClosed k] [IsMonHom r] in
theorem isConstructible_identityComponentRange : IsConstructible r.identityComponentRange := by
  have : IsNoetherianRing (CoordinateRing m k) := Algebra.FiniteType.isNoetherianRing k _
  rw [identityComponentRange, ← Set.image_univ]
  refine PrimeSpectrum.isConstructible_comap_image ?_ .univ
  refine RingHom.FinitePresentation.of_finiteType.1 ?_
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (CoordinateRing m k)) ?_
  rw [AlgHom.comp_algebraMap]
  exact RingHom.finiteType_algebraMap.2 inferInstance

omit [IsMonHom r] in
theorem isIrreducible_closure_identityComponentRange :
    IsIrreducible (closure r.identityComponentRange) := by
  have : (identityComponent I).IsPrime := isPrime_identityComponent I
  rw [identityComponentRange, ← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ _).image _
    (PrimeSpectrum.continuous_comap _).continuousOn).closure

theorem image_closure_subset_of_mem {a b : GL m k} (ha : a ∈ r.identityComponentImage)
    (hb : b ∈ r.identityComponentImage) :
    translateHomeomorph a b '' closure (toPrimeSpectrum '' (r.identityComponentImage :
      Set (GL m k))) ⊆ closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k))) := by
  refine (image_closure_subset_closure_image (translateHomeomorph a b).continuous).trans
    (closure_mono ?_)
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  exact ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hs) hb,
    (translateHomeomorph_toPrimeSpectrum a b s).symm⟩

theorem invHomeomorph_image_closure_subset :
    invHomeomorph '' closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k))) ⊆
      closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k))) := by
  refine (image_closure_subset_closure_image invHomeomorph.continuous).trans (closure_mono ?_)
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  exact ⟨_, Subgroup.inv_mem _ hs, (invHomeomorph_toPrimeSpectrum s).symm⟩

theorem image_closure_subset_of_toPrimeSpectrum_mem {t : GL m k}
    (ht : toPrimeSpectrum t ∈
      closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k)))) :
    translateHomeomorph t 1 '' closure (toPrimeSpectrum '' (r.identityComponentImage :
      Set (GL m k))) ⊆ closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k))) := by
  refine (image_closure_subset_closure_image (translateHomeomorph t 1).continuous).trans
    (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  have := r.image_closure_subset_of_mem (Subgroup.one_mem _) hs ⟨_, ht, rfl⟩
  rwa [translateHomeomorph_toPrimeSpectrum, one_mul, ← mul_one (t * s),
    ← translateHomeomorph_toPrimeSpectrum] at this

/-- Every `k`-point of the closure `T` of the image of `G°` lies in `r(G°(k))`. -/
theorem mem_identityComponentImage_of_mem_closure {x : GL m k}
    (hx : toPrimeSpectrum x ∈
      closure (toPrimeSpectrum '' (r.identityComponentImage : Set (GL m k)))) :
    x ∈ r.identityComponentImage := by
  have : IsNoetherianRing (CoordinateRing m k) := Algebra.FiniteType.isNoetherianRing k _
  have : IsJacobsonRing (CoordinateRing m k) := isJacobsonRing_of_finiteType (A := k)
  set S₀ := r.identityComponentImage
  set T := closure (toPrimeSpectrum '' (S₀ : Set (GL m k)))
  obtain ⟨U, hU, hUT, hUY⟩ := exists_isOpen_inter_subset_of_isConstructible
    r.isConstructible_identityComponentRange isClosed_closure
    r.isIrreducible_closure_identityComponentRange rfl
  rw [closure_identityComponentRange] at hUT hUY
  have hT_inv_mem (t : GL m k) (ht : toPrimeSpectrum t ∈ T) : toPrimeSpectrum t⁻¹ ∈ T :=
    r.invHomeomorph_image_closure_subset ⟨_, ht, invHomeomorph_toPrimeSpectrum t⟩
  set Φ := invHomeomorph.trans (translateHomeomorph x 1)
  have hΦT : Φ '' T = T := by
    refine Set.Subset.antisymm ?_ fun p hp ↦ ⟨invHomeomorph (translateHomeomorph x⁻¹ 1 p), ?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact r.image_closure_subset_of_toPrimeSpectrum_mem hx
        ⟨_, r.invHomeomorph_image_closure_subset ⟨p, hp, rfl⟩, rfl⟩
    · exact r.invHomeomorph_image_closure_subset ⟨_,
        r.image_closure_subset_of_toPrimeSpectrum_mem (hT_inv_mem x hx) ⟨p, hp, rfl⟩, rfl⟩
    · change translateHomeomorph x 1 (invHomeomorph (invHomeomorph _)) = p
      rw [invHomeomorph_invHomeomorph, translateHomeomorph_translateHomeomorph, mul_inv_cancel,
        mul_one, translateHomeomorph_one_one_apply]
  have hTirr : IsIrreducible T := by
    have := r.isIrreducible_closure_identityComponentRange
    rwa [closure_identityComponentRange] at this
  obtain ⟨p₀, hp₀U, hp₀T⟩ := hUT
  have hW : (T ∩ Φ '' U).Nonempty := by
    refine ⟨Φ p₀, ?_, Set.mem_image_of_mem Φ hp₀U⟩
    rw [← hΦT]
    exact Set.mem_image_of_mem Φ hp₀T
  obtain ⟨w, hwT, hwU, hwΦ⟩ := hTirr.2 U (Φ '' U) hU (Φ.isOpenMap U hU) ⟨p₀, hp₀T, hp₀U⟩ hW
  obtain ⟨q, ⟨hqT, hqU, hqΦ⟩, hq⟩ := nonempty_inter_closedPoints (Z := T ∩ (U ∩ Φ '' U))
    ⟨w, hwT, hwU, hwΦ⟩ (isClosed_closure.isLocallyClosed.inter
      (hU.inter (Φ.isOpenMap U hU)).isLocallyClosed)
  obtain ⟨z, rfl⟩ := exists_toPrimeSpectrum_eq_of_mem_closedPoints hq
  have hz : z ∈ S₀ := r.mem_identityComponentImage_of_mem_range (hUY ⟨hqU, hqT⟩)
  obtain ⟨p, hpU, hpz⟩ := hqΦ
  have hp : p = toPrimeSpectrum (z⁻¹ * x) := by
    rw [← Φ.symm_apply_apply p, hpz]
    change invHomeomorph (translateHomeomorph x⁻¹ 1⁻¹ (toPrimeSpectrum z)) = _
    rw [translateHomeomorph_toPrimeSpectrum, invHomeomorph_toPrimeSpectrum]
    congr 1
    simp
  have hpT : p ∈ T := by
    rw [← hΦT] at hqT
    obtain ⟨p', hp'T, hp'⟩ := hqT
    rwa [← Φ.injective (hp'.trans hpz.symm)]
  have : z⁻¹ * x ∈ S₀ := r.mem_identityComponentImage_of_mem_range (hUY ⟨hp ▸ hpU, hp ▸ hpT⟩)
  simpa using S₀.mul_mem hz this

/-- The image of `G(k)` under `r` is the set of `k`-points of its Zariski closure, in terms of
the matrix group `zeroLocus I k`. -/
theorem mem_range_zeroLocusPoints_iff {x : GL m k} :
    x ∈ r.zeroLocusPoints.range ↔
      ∀ a ∈ vanishingIdeal (r.zeroLocusPoints.range : Set (GL m k)), evalAlgHom x a = 0 := by
  refine ⟨fun hx a ha ↦ mem_vanishingIdeal.1 ha x hx, fun hx ↦ ?_⟩
  set H := (zeroLocus (identityComponent I) k).subgroupOf (zeroLocus I k)
  set S₀ := r.identityComponentImage
  set T := closure (toPrimeSpectrum '' (S₀ : Set (GL m k)))
  have hPT : toPrimeSpectrum '' (S₀ : Set (GL m k)) ⊆ T := subset_closure
  have : H.FiniteIndex := finiteIndex_zeroLocus_identityComponent I
  let F (g : zeroLocus I k) : Set (PrimeSpectrum (CoordinateRing m k)) :=
    translateHomeomorph (r.zeroLocusPoints g) 1 '' T
  have hTstab (h : zeroLocus I k) (hh : h ∈ H) :
      translateHomeomorph (r.zeroLocusPoints h) 1 '' T = T := by
    have hs : r.zeroLocusPoints h ∈ S₀ := Subgroup.mem_map_of_mem r.zeroLocusPoints hh
    refine (r.image_closure_subset_of_toPrimeSpectrum_mem (hPT ⟨_, hs, rfl⟩)).antisymm
      fun p hp ↦ ⟨translateHomeomorph (r.zeroLocusPoints h)⁻¹ 1 p,
        r.image_closure_subset_of_toPrimeSpectrum_mem (hPT ⟨_, S₀.inv_mem hs, rfl⟩) ⟨p, hp, rfl⟩,
        ?_⟩
    rw [translateHomeomorph_translateHomeomorph, mul_inv_cancel, mul_one,
      translateHomeomorph_one_one_apply]
  have hF (g h : zeroLocus I k) (hh : h ∈ H) : F (g * h) = F g := by
    change translateHomeomorph _ 1 '' T = translateHomeomorph _ 1 '' T
    conv_rhs => rw [← hTstab h hh, ← Set.image_comp]
    refine congrArg (· '' T) (funext fun p ↦ ?_)
    rw [Function.comp_apply, translateHomeomorph_translateHomeomorph, map_mul, one_mul]
  have hFfin : (Set.range F).Finite := by
    have : Finite (zeroLocus I k ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    let F' : zeroLocus I k ⧸ H → Set (PrimeSpectrum (CoordinateRing m k)) :=
      Quotient.lift (s := QuotientGroup.leftRel H) F fun a b hab ↦ by
        rw [← hF a (a⁻¹ * b) (QuotientGroup.leftRel_apply.1 hab), mul_inv_cancel_left]
    refine (Set.finite_range F').subset ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨Quotient.mk _ g, rfl⟩
  have hZ : IsClosed (⋃ s ∈ Set.range F, s) := hFfin.isClosed_biUnion fun _ ⟨g, hg⟩ ↦
    hg ▸ (translateHomeomorph _ 1).isClosedMap _ isClosed_closure
  have hSZ :
      toPrimeSpectrum '' (r.zeroLocusPoints.range : Set (GL m k)) ⊆ ⋃ s ∈ Set.range F, s := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    refine Set.mem_biUnion (x := F g) ⟨g, rfl⟩ ⟨toPrimeSpectrum 1, hPT ⟨1, S₀.one_mem, rfl⟩, ?_⟩
    rw [translateHomeomorph_toPrimeSpectrum, mul_one, mul_one]
  have hxcl : toPrimeSpectrum x ∈
      closure (toPrimeSpectrum '' (r.zeroLocusPoints.range : Set (GL m k))) := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro a ha
    refine hx a (mem_vanishingIdeal.2 fun y hy ↦ ?_)
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha _ ⟨y, hy, rfl⟩
  obtain ⟨_, ⟨g, rfl⟩, p, hpT, hpx⟩ := Set.mem_iUnion₂.1 (closure_minimal hSZ hZ hxcl)
  have hp : p = toPrimeSpectrum ((r.zeroLocusPoints g)⁻¹ * x) := by
    rw [← mul_one ((r.zeroLocusPoints g)⁻¹ * x), ← translateHomeomorph_toPrimeSpectrum, ← hpx,
      translateHomeomorph_translateHomeomorph, inv_mul_cancel, mul_one,
      translateHomeomorph_one_one_apply]
  obtain ⟨h, -, hh⟩ := r.mem_identityComponentImage_of_mem_closure (hp ▸ hpT)
  exact ⟨g * h, by rw [map_mul, hh, mul_inv_cancel_left]⟩

/-- **The image of a homomorphism of matrix groups is closed.** Let `G = V(I) ⊆ GL_n` be a
closed subgroup over an algebraically closed field `k` and `r : G ⟶ GL_m` a homomorphism. The
image `S = r(G(k))` of the `k`-points is Zariski closed: a matrix on which every equation vanishing
on `S` vanishes lies in `S`. So `S` is the set of `k`-points of the reduced closed subgroup
`V(vanishingIdeal S)` of `GL_m`.

The image of `G°` is constructible with irreducible closure `T`, hence contains a nonempty open
`U ∩ T`; for a `k`-point `x` of `T`, the open subsets `U ∩ T` and `x (U ∩ T)⁻¹` of `T` meet in a
`k`-point `z`, so that `x = z (z⁻¹ x) ∈ r(G°(k))`. Then `S` is the finite union of the translates
of `T` by `r` of coset representatives of `G°(k)` in `G(k)`.
(blueprint: `lemma-connected-components-images-homomorphisms--2`) -/
theorem mem_range_points_iff {x : GL m k} :
    x ∈ (r.points k).range ↔
      ∀ a ∈ vanishingIdeal ((r.points k).range : Set (GL m k)), evalAlgHom x a = 0 := by
  rw [← range_zeroLocusPoints]
  exact r.mem_range_zeroLocusPoints_iff

end RationalHom

end AlgebraicGeometry.GeneralLinearGroup
