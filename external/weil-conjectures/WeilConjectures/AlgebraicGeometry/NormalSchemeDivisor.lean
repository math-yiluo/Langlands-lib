/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Local rings of normal schemes at generic points of principal divisors

On a locally noetherian normal scheme `X`, the local ring at a generic point of an irreducible
component of the zero locus of a nonzero global function is a discrete valuation ring.
This is the first step of the proof of blueprint `lemma-vanishing-generic-points-principal-divisor`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing Topology

namespace AlgebraicGeometry.Scheme

/-- The preimage of `X.basicOpen f` under `Spec 𝒪_{X,x} ⟶ X` is the basic open set of the germ
of `f` at `x`. -/
lemma fromSpecStalk_mem_basicOpen_top_iff {X : Scheme.{u}} (x : X) (f : Γ(X, ⊤))
    (p : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ X.basicOpen f ↔ X.presheaf.germ ⊤ x trivial f ∉ p.asIdeal := by
  rw [← Hom.mem_preimage, preimage_basicOpen_top, fromSpecStalk_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, basicOpen_res, basicOpen_eq_of_affine, top_inf_eq]
  exact Iff.rfl

/-- If `x` lies in the zero locus of `f` and no proper generalization of `x` does, then the
maximal ideal of `𝒪_{X,x}` is a minimal prime over the germ of `f`. -/
lemma maximalIdeal_stalk_mem_minimalPrimes {X : Scheme.{u}} {f : Γ(X, ⊤)} {x : X}
    (hx : x ∈ X.zeroLocus (U := ⊤) {f})
    (hgen : ∀ y ∈ X.zeroLocus (U := ⊤) {f}, y ⤳ x → y = x) :
    maximalIdeal (X.presheaf.stalk x) ∈
      (Ideal.span {X.presheaf.germ ⊤ x trivial f}).minimalPrimes := by
  have hxf : x ∉ X.basicOpen f := (X.mem_zeroLocus_iff _ x).1 hx f rfl
  refine ⟨⟨inferInstance, ?_⟩, fun q ⟨hq, hfq⟩ hqm ↦ ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal,
      mem_nonunits_iff, ← mem_basicOpen_top]
    exact hxf
  · let p : Spec (X.presheaf.stalk x) := ⟨q, hq⟩
    have hp : X.fromSpecStalk x p = X.fromSpecStalk x (closedPoint _) := by
      rw [fromSpecStalk_closedPoint]
      refine hgen _ ((X.mem_zeroLocus_iff _ _).2 ?_) ?_
      · rintro g rfl
        rw [fromSpecStalk_mem_basicOpen_top_iff, not_not]
        exact hfq (Ideal.subset_span rfl)
      · simpa using (specializes_closedPoint p).map (X.fromSpecStalk x).continuous
    exact (congrArg PrimeSpectrum.asIdeal ((X.fromSpecStalk x).isEmbedding.injective hp)).ge

/-- A noetherian integrally closed local domain whose maximal ideal is minimal over a nonzero
principal ideal is a discrete valuation ring (Krull's principal ideal theorem and Serre's
criterion in dimension one). -/
lemma _root_.IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0)
    (hm : maximalIdeal R ∈ (Ideal.span {a}).minimalPrimes) : IsDiscreteValuationRing R := by
  have hnf : ¬ IsField R := by
    intro hF
    have ham : a ∈ maximalIdeal R := hm.1.2 (Ideal.subset_span rfl)
    rw [isField_iff_maximalIdeal_eq.1 hF, Ideal.mem_bot] at ham
    exact ha ham
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hm
  have : Ring.DimensionLEOne R := ⟨fun hp hpr ↦ hpr.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain R := {}
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 3).2 this

/-- At a generic point `ζ` of the zero locus of a nonzero global function `h` on a locally
noetherian normal scheme, the local ring is a discrete valuation ring (Krull's principal ideal
theorem and Serre's criterion R₁). First step of the proof of blueprint
`lemma-vanishing-generic-points-principal-divisor`. -/
theorem isDiscreteValuationRing_stalk_of_mem_irreducibleComponents
    {X : Scheme.{u}} (hX : IsNormalScheme X) [IsLocallyNoetherian X] {h : Γ(X, ⊤)} (hh : h ≠ 0)
    (ζ : X.zeroLocus (U := ⊤) {h})
    (hζ : closure {ζ} ∈ irreducibleComponents (X.zeroLocus (U := ⊤) {h})) :
    haveI := hX.1
    IsDiscreteValuationRing (X.presheaf.stalk ζ.1) := by
  have := hX.1
  have := (hX.2 ζ.1).2
  refine IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
    ((map_ne_zero_iff _ (germ_injective_of_isIntegral X (U := ⊤) ζ.1 trivial)).2 hh)
    (maximalIdeal_stalk_mem_minimalPrimes ζ.2 fun y hy hyζ ↦ ?_)
  have hspec : (⟨y, hy⟩ : X.zeroLocus (U := ⊤) {h}) ⤳ ζ :=
    IsInducing.subtypeVal.specializes_iff.1 hyζ
  have hle := hζ.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.1 hspec)
  exact congrArg Subtype.val (hspec.antisymm (specializes_iff_closure_subset.2 hle)).eq

end AlgebraicGeometry.Scheme
