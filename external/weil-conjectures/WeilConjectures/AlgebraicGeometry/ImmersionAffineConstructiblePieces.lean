/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible
import WeilConjectures.RingTheory.AffineBasicSetsDisjointRefinement
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Affine constructible pieces of an immersed scheme

Source: literature/stacks-project/etale-cohomology.tex, Etale Cohomology, Lemma Tag 03S0,
proof, line 12049 (blueprint: lem-weil-pbc-immersion-affine-constructible-pieces).
-/

@[expose] public section

open CategoryTheory
open Topology
namespace AlgebraicGeometry

/-- Realize a basic constructible set by the spectrum of a localized quotient.
Source: Stacks Project, Algebra, proof of Tag 00F8, lines 5467–5471, with Tags 00E4
and 00E5 (blueprint: lem-weil-pbc-basic-subset-immersion-image).
The quotient spectrum is a closed immersion, the localization spectrum is an open
immersion, and the range calculation is the image of a basic open under the quotient map. -/
private theorem basic_constructible_affine_immersion
    {A : Type*} [CommRing A] (C : PrimeSpectrum.BasicConstructibleSetData A) :
    ∃ (W : Scheme) (w : W ⟶ Spec (CommRingCat.of A)),
      IsAffine W ∧ IsImmersion w ∧ Set.range w = C.toSet := by
  let I := Ideal.span (Set.range C.g)
  let f := Ideal.Quotient.mk I C.f
  let W := Spec (CommRingCat.of (Localization.Away f))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j := Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) (Localization.Away f)))
  have hj : IsOpenImmersion j := by
    dsimp [j]
    infer_instance
  have hq : IsClosedImmersion q := by
    dsimp [q]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨W, j ≫ q, inferInstance, inferInstance, ?_⟩
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I) ∘
    PrimeSpectrum.comap (algebraMap (A ⧸ I) (Localization.Away f))) = C.toSet
  rw [Set.range_comp, PrimeSpectrum.localization_away_comap_range _ f,
    ← PrimeSpectrum.comap_basicOpen, TopologicalSpace.Opens.coe_comap,
    ContinuousMap.coe_mk, Set.image_preimage_eq_inter_range,
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    PrimeSpectrum.BasicConstructibleSetData.toSet, Set.sdiff_eq_compl_inter,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]

set_option backward.isDefEq.respectTransparency false in
/--
An immersion into an affine scheme whose image is constructible admits a finite
partition by affine schemes mapping by immersions to pairwise disjoint locally
closed constructible pieces.
Source: literature/stacks-project/etale-cohomology.tex, Etale Cohomology, Lemma Tag 03S0,
proof, line 12049 (blueprint: lem-weil-pbc-immersion-affine-constructible-pieces).

Proof (the six steps of the node):
1. Choose an isomorphism `X ≅ Spec A` using `def-pc-scheme` and
   `def-weil-affine-spectrum`. It and its inverse are open immersions
   (`def-weil-open-immersion`), hence immersions (`def-weil-closed-immersion`).
   Composition preserves immersions (`lem-weil-pbc-proper-fp-permanence`, clause (e)).
   The underlying homeomorphism preserves constructibility, local closedness,
   disjointness and unions (`def-weil-constructible-subset`,
   `def-weil-locally-closed-subset`), so it suffices to treat `X = Spec A`.
2. Write `E` as a finite union of basic sets `D(f) ∩ V(g₁, ..., gₙ)` using
   `lem-weil-pbc-affine-constructible-basic-union`. Refine to finitely many pairwise
   disjoint basic sets `Eₖ` using `lem-weil-pbc-affine-basic-sets-disjoint-refinement`.
   The index set may be empty.
3. For each piece put `Jₖ = (g₁, ..., gₙ)`, `Rₖ = (A/Jₖ)[1/f]`, and `Wₖ = Spec Rₖ`.
   The induced map `wₖ : Wₖ ⟶ X` is an immersion with image `Eₖ` by
   `lem-weil-pbc-basic-subset-immersion-image`.
4. Set `Zₖ = Z ×_X Wₖ` (`def-pc-fibre-product`) with projections `κₖ : Zₖ ⟶ Z`
   and `qₖ : Zₖ ⟶ Wₖ`. Both are immersions, being base changes of `wₖ` and `ι`
   (`lem-weil-pbc-immersion-base-change-lft`, clause (1)), and `κₖ ≫ ι = qₖ ≫ wₖ`.
5. By `lem-weil-pbc-base-change-image`, the image of `qₖ` is `wₖ⁻¹(E) = Wₖ`,
   since `Eₖ ⊆ E`. Thus `qₖ` is a closed immersion by
   `lem-weil-pbc-immersion-closed-image-closed-immersion`. Its target is affine
   (`def-weil-affine-spectrum`), so `Zₖ` is affine by
   `lem-weil-pbc-closed-immersion-affine-cover-criterion`, clause (1).
6. The composite `κₖ ≫ ι = qₖ ≫ wₖ` is an immersion by
   `lem-weil-pbc-proper-fp-permanence`, clause (e), with image `wₖ(Wₖ) = Eₖ`.
   Each basic set is locally closed (`def-weil-locally-closed-subset`) and constructible
   (`lem-weil-pbc-affine-constructible-basic-union`). Step 2 gives disjointness and
   union `E`, and step 5 gives affineness, as required.
-/
theorem exists_finite_affine_immersion_constructible_pieces
    {X Z : Scheme} (hX : IsAffine X) (ι : Z ⟶ X) [IsImmersion ι]
    (E : Set X) (hE : E = Set.range ι) (hEc : IsConstructible E) :
    ∃ (K : Type) (_ : Fintype K) (Zk : K → Scheme)
      (κ : ∀ k, Zk k ⟶ Z) (Ek : K → Set X),
      (∀ k, IsAffine (Zk k)) ∧
      (∀ k, IsImmersion (κ k)) ∧
      (∀ k, IsImmersion (κ k ≫ ι)) ∧
      (∀ k, Set.range (κ k ≫ ι) = Ek k) ∧
      (∀ k, IsLocallyClosed (Ek k)) ∧
      (∀ k, IsConstructible (Ek k)) ∧
      (Set.PairwiseDisjoint Set.univ Ek) ∧
      E = ⋃ k, Ek k := by
  classical
  let : IsAffine X := hX
  let e := X.isoSpec.hom.homeomorph
  have hEc' : IsConstructible (e '' E) :=
    hEc.image_of_isOpenEmbedding e.isOpenEmbedding (by
      rw [e.surjective.range_eq]
      exact IsRetrocompact.univ)
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hEc'
  let B (i : Fin (Fintype.card S)) := ((Fintype.equivFin S).symm i).val
  have hB : (⋃ i, (B i).toSet) = e '' E := by
    rw [← hS]
    ext x
    simp only [Set.mem_iUnion, PrimeSpectrum.ConstructibleSetData.toSet]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨B i, ((Fintype.equivFin S).symm i).property, hi⟩
    · rintro ⟨C, hC, hx⟩
      refine ⟨Fintype.equivFin S ⟨C, hC⟩, ?_⟩
      simpa [B] using hx
  obtain ⟨p, C, hdis, hC⟩ :=
    PrimeSpectrum.finite_disjoint_basic_constructible_refinement _ B
  have hpartition : E = ⋃ k, e ⁻¹' (C k).toSet := by
    rw [← Set.preimage_iUnion, ← hC, hB, e.preimage_image]
  choose W w hW hw hr using fun k ↦ basic_constructible_affine_immersion (C k)
  let v (k : Fin p) : W k ⟶ X := w k ≫ X.isoSpec.inv
  have hv (k : Fin p) : IsImmersion (v k) := by
    have := hw k
    dsimp [v]
    infer_instance
  have hvr (k : Fin p) : Set.range (v k) = e ⁻¹' (C k).toSet := by
    rw [show (v k : W k → X) = X.isoSpec.inv ∘ w k from rfl,
      Set.range_comp, hr k]
    exact e.symm.image_eq_preimage_symm _
  have hsub (k : Fin p) : Set.range (v k) ⊆ E := by
    rw [hvr, hpartition]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨k, hx⟩
  let Zk (k : Fin p) := Limits.pullback ι (v k)
  let κ (k : Fin p) : Zk k ⟶ Z := Limits.pullback.fst ι (v k)
  have hsurj (k : Fin p) : Set.range (Limits.pullback.snd ι (v k)) = Set.univ := by
    rw [Scheme.Pullback.range_snd, ← hE]
    exact Set.eq_univ_of_forall fun x ↦ hsub k ⟨x, rfl⟩
  have hclosed (k : Fin p) : IsClosedImmersion (Limits.pullback.snd ι (v k)) := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [hsurj]
    exact isClosed_univ
  have haff (k : Fin p) : IsAffine (Zk k) := by
    have := hW k
    have := hclosed k
    exact isAffine_of_isAffineHom (Limits.pullback.snd ι (v k))
  have hκ (k : Fin p) : IsImmersion (κ k) := by
    have := hv k
    dsimp [κ]
    infer_instance
  have hcomp (k : Fin p) : IsImmersion (κ k ≫ ι) := by
    have := hκ k
    infer_instance
  have hrange (k : Fin p) : Set.range (κ k ≫ ι) = e ⁻¹' (C k).toSet := by
    rw [Scheme.Pullback.range_fst_comp, ← hE, Set.inter_eq_right.mpr (hsub k), hvr]
  refine ⟨Fin p, inferInstance, Zk, κ, fun k ↦ e ⁻¹' (C k).toSet,
    haff, hκ, hcomp, hrange, ?_, ?_, ?_, hpartition⟩
  · intro k
    dsimp only
    rw [← hrange k]
    have := hcomp k
    exact (κ k ≫ ι).isLocallyClosed_range
  · intro k
    apply IsConstructible.preimage_of_isOpenEmbedding e.isOpenEmbedding
    have hc := (PrimeSpectrum.ConstructibleSetData.isConstructible_toSet {C k})
    simpa [PrimeSpectrum.ConstructibleSetData.toSet] using hc
  · intro i _ j _ hij
    exact (hdis hij).preimage e

end AlgebraicGeometry
