/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.GenericFiniteOpenNeighborhood

/-! The geometric shrinking step for a dense open in a relative affine line. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.AffineSpace

private theorem genericPoint_mem_dense_open
    {T : Type u} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    {C : Set T} (hC : C ∈ irreducibleComponents T) {η : T}
    (hη : IsGenericPoint η C) (U : TopologicalSpace.Opens T) (hU : Dense (U : Set T)) :
    η ∈ U := by
  classical
  let I := ↥(irreducibleComponents T)
  have : Finite I := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let Z : I := ⟨C, hC⟩
  let O : TopologicalSpace.Opens T := ⟨⋂ Z' ∈ ({Z}ᶜ : Set I), Z'.1ᶜ,
    (Set.toFinite _).isOpen_biInter fun Z' _ ↦
      (isClosed_of_mem_irreducibleComponents _ Z'.2).isOpen_compl⟩
  have hηO : η ∈ O := by
    refine Set.mem_iInter₂.2 fun Z' hZ' hηZ' ↦ hZ' ?_
    have hsub : C ⊆ Z'.1 := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.2 hηZ')
        (isClosed_of_mem_irreducibleComponents _ Z'.2)
    exact (Subtype.ext (hC.eq_of_le Z'.2.1 hsub)).symm
  obtain ⟨x, hxO, hxU⟩ := hU.inter_open_nonempty O O.isOpen ⟨η, hηO⟩
  obtain ⟨C', hC', hxC'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have heq : (⟨C', hC'⟩ : I) = Z := by
    by_contra hn
    exact Set.mem_iInter₂.1 hxO ⟨C', hC'⟩ hn (hxC' rfl)
  have heq' : C' = C := congrArg Subtype.val heq
  have hxC : x ∈ C := heq' ▸ hxC' rfl
  exact (hη.specializes hxC).mem_open U.isOpen hxU

private theorem exists_dense_basicOpen
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) (hU : Dense (U : Set (PrimeSpectrum R))) :
    ∃ r : R, PrimeSpectrum.basicOpen r ≤ U ∧
      Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  classical
  let J := PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))ᶜ
  have hnot (p : Ideal R) (hp : p ∈ minimalPrimes R) : ¬ J ≤ p := by
    let q : PrimeSpectrum R := ⟨p, hp.1.1⟩
    have hC : PrimeSpectrum.zeroLocus (p : Set R) ∈
        irreducibleComponents (PrimeSpectrum R) := by
      rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact ⟨p, hp, rfl⟩
    have hq : IsGenericPoint q (PrimeSpectrum.zeroLocus (p : Set R)) :=
      PrimeSpectrum.closure_singleton q
    have hqU := genericPoint_mem_dense_open hC hq U hU
    intro hJ
    have hqC : q ∈ (U : Set (PrimeSpectrum R))ᶜ := by
      rw [← U.isOpen.isClosed_compl.closure_eq,
        ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hJ
    exact hqC hqU
  have havoid : ¬ (J : Set R) ⊆ ⋃ p ∈ minimalPrimes R, (p : Set R) := by
    rw [Ideal.subset_union_prime_finite (minimalPrimes.finite_of_isNoetherianRing R)
      (⊥ : Ideal R) ⊥ (fun p hp _ _ ↦ hp.1.1)]
    rintro ⟨p, hp, hJ⟩
    exact hnot p hp hJ
  obtain ⟨r, hrJ, hr⟩ := Set.not_subset.mp havoid
  have hrp (p : Ideal R) (hp : p ∈ minimalPrimes R) : r ∉ p := by
    intro hrp
    exact hr (Set.mem_iUnion₂.mpr ⟨p, hp, hrp⟩)
  refine ⟨r, ?_, ?_⟩
  · intro p hp
    by_contra hpU
    exact hp ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hrJ p hpU)
  · rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨m, hm, hmp⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    let q : PrimeSpectrum R := ⟨m, hm.1.1⟩
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hmp).mem_closed isClosed_closure
      (subset_closure (hrp m hm))

private theorem finite_generic_fibers
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherian Y]
    (U : (AffineSpace (ULift.{u} (Fin 1)) Y).Opens)
    (hU : Dense (U : Set (AffineSpace (ULift.{u} (Fin 1)) Y))) :
    ∀ C ∈ irreducibleComponents Y, ∀ η : Y, IsGenericPoint η C →
      ((Scheme.Opens.closedComplement U ≫
        (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) ⁻¹' {η}).Finite := by
  classical
  let n := ULift.{u} (Fin 1)
  let X := AffineSpace n Y
  let f : X ⟶ Y := X ↘ Y
  let V : Y.Opens := ⟨f '' (U : Set X), AffineSpace.isOpenMap_over (n := n) Y (U : Set X) U.isOpen⟩
  have hVd : Dense (V : Set Y) := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact image_closure_subset_closure_image f.continuous ⟨x, hU x, rfl⟩
  intro C hC η hη
  obtain ⟨x, hxU, hxy⟩ := genericPoint_mem_dense_open hC hη V hVd
  let g := Y.fromSpecResidueField η
  let X' := AffineSpace n (Spec (Y.residueField η))
  let a := AffineSpace.map n g
  let sq := AffineSpace.isPullback_map (n := n) g
  let e : X' ≅ f.fiber η := sq.isoPullback
  let O : Set X' := a ⁻¹' (U : Set X)
  have hO : IsOpen O := U.isOpen.preimage a.continuous
  have hOne : O.Nonempty := by
    let z := f.fiberHomeo η |>.symm ⟨x, hxy⟩
    refine ⟨e.inv z, ?_⟩
    change a (e.inv z) ∈ U
    have ha : a (e.inv z) = x := by
      calc
        a (e.inv z) = f.fiberι η z :=
          congrArg (fun k ↦ k z) sq.isoPullback_inv_fst
        _ = x := f.fiberι_fiberHomeo_symm η _
    exact ha.symm ▸ hxU
  have : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType (X' ↘ Spec (Y.residueField η))
  have hdim : topologicalKrullDim X' ≤ 1 := by
    rw [topologicalKrullDim_affineSpace_of_isAffine]
    calc
      _ ≤ 0 + 1 := add_le_add (topologicalKrullDim_zero_of_discreteTopology _)
        (by norm_num [n, Nat.card_eq_fintype_card])
      _ = 1 := by simp
  have hb : Oᶜ.Finite := hO.finite_compl_of_topologicalKrullDim_le_one hdim hOne
  have hbf : (f.fiberι η ⁻¹' (U : Set X))ᶜ.Finite := by
    refine (hb.image (Scheme.homeoOfIso e)).subset ?_
    intro z hz
    refine ⟨e.inv z, ?_, by
      change e.hom (e.inv z) = z
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl⟩
    change a (e.inv z) ∉ U
    have ha := congrArg (fun k ↦ k z) sq.isoPullback_inv_fst
    simpa only [Scheme.Hom.comp_apply] using (ha.symm ▸ hz)
  refine ((hbf.image (f.fiberι η)).preimage
    (Scheme.Opens.closedComplement U).isClosedEmbedding.injective.injOn).subset ?_
  intro z hz
  refine ⟨(f.fiberHomeo η).symm ⟨(Scheme.Opens.closedComplement U) z, hz⟩, ?_,
    f.fiberι_fiberHomeo_symm η _⟩
  rw [Set.mem_compl_iff, Set.mem_preimage, Scheme.Hom.fiberι_fiberHomeo_symm]
  have hzi : (Scheme.Opens.closedComplement U) z ∈ (U : Set X)ᶜ := by
    exact (Scheme.Opens.range_closedComplement U).subset ⟨z, rfl⟩
  exact hzi

/-- The closed complement of a dense open of a relative affine line becomes finite over a
suitable dense affine open of a finite-type integer base.
Source: Stacks Project, Tag 0GKZ, dense-open step, and Tag 02NW.
(blueprint: lem-weil-pbc-affine-line-dense-open-finite-complement)

Proof: The projection is open, continuous and surjective, so the image of the dense
open U is a dense open of the base. It contains every component generic point: remove the
other finitely many components and use density there, then specialize from the generic
point. Thus U meets each generic fibre. Such a fibre is an affine line over a residue
field; its nonempty open has finite complement by irreducibility, Noetherianity and the
dimension-one bound. Injectivity of the closed immersion gives finite generic fibres for
the closed complement. Apply the generic-finiteness neighborhood theorem to obtain a
dense open V over which the complement is finite. To find a dense principal open W in V,
apply finite prime avoidance to the ideal defining the complement of V: it is contained
in none of the finitely many minimal primes. Its chosen element avoids all minimal primes,
so its principal open is dense. W is affine and finite type over the integers. Identify
W with its affine spectrum and pull back the original closed complement to the relative
line over W. The cartesian squares for restriction and affine space identify its projection
as a base change of the finite morphism over V. This constructs the closed subscheme and
proves finiteness without identifying reduced scheme structures. Every step also applies
to the empty base and to nonreduced bases. -/
theorem exists_dense_affine_open_isFinite_closedComplement
    (Y : Scheme.{u}) [IsAffine Y] [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (U : (AffineSpace (ULift.{u} (Fin 1)) Y).Opens)
    (hU : Dense (U : Set (AffineSpace (ULift.{u} (Fin 1)) Y))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
      (g : Spec (.of R) ⟶ Y) (_ : IsOpenImmersion g),
      Dense (Set.range g.base) ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)))
        (_ : IsClosedImmersion i),
        Set.range i.base =
          ((AffineSpace.map (ULift.{u} (Fin 1)) g ⁻¹ᵁ U :
            (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens) : Set _)ᶜ ∧
        IsFinite (i ≫
          (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))) := by
  classical
  have : IsNoetherianRing Γ(Y, ⊤) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType Y.isoSpec.hom
  let n := ULift.{u} (Fin 1)
  let X := AffineSpace n Y
  let f : X ⟶ Y := X ↘ Y
  let i₀ := Scheme.Opens.closedComplement U
  let h := i₀ ≫ f
  obtain ⟨V, hVd, _, hVf⟩ :=
    Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers h
      (finite_generic_fibers Y U hU)
  let V' := Y.isoSpec.inv ⁻¹ᵁ V
  have hV'd : Dense (V' : Set (Spec Γ(Y, ⊤))) :=
    hVd.preimage (Scheme.homeoOfIso Y.isoSpec).symm.isOpenMap
  obtain ⟨r, hrV, hrd⟩ := exists_dense_basicOpen Γ(Y, ⊤) V' hV'd
  let W := Y.basicOpen r
  have hWeq : Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r = W :=
    Scheme.map_PrimeSpectrum_basicOpen_of_affine Y r
  have : IsAffine W.toScheme := (isAffineOpen_top Y).basicOpen r
  have : TopologicalSpace.NoetherianSpace W.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (W : Set Y))
  have hWd : Dense (W : Set Y) := by
    rw [← hWeq]
    exact hrd.preimage (Scheme.homeoOfIso Y.isoSpec).isOpenMap
  have hWV : W ≤ V := by
    intro y hy
    have hy' : Y.isoSpec.hom y ∈ PrimeSpectrum.basicOpen r := by
      have hy' : y ∈ Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r := hWeq.symm ▸ hy
      exact hy'
    have hy'' := hrV hy'
    change Y.isoSpec.inv (Y.isoSpec.hom y) ∈ V at hy''
    exact (Scheme.homeoOfIso Y.isoSpec).symm_apply_apply y ▸ hy''
  let R := Γ(W.toScheme, ⊤)
  have : Algebra.FiniteType ℤ R := by
    let : Algebra Γ(Y, ⊤) R := W.ι.appTop.hom.toAlgebra
    have : Algebra.FiniteType Γ(Y, ⊤) R := (RingHom.finiteType_algebraMap).mp
      (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) W.ι inferInstance)
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ Γ(Y, ⊤))
      (inferInstance : Algebra.FiniteType Γ(Y, ⊤) R)
  let g := W.toScheme.isoSpec.inv ≫ W.ι
  have hgd : Dense (Set.range g.base) := by
    change Dense (g.opensRange : Set Y)
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    simpa only [Scheme.Opens.opensRange_ι] using hWd
  let a := AffineSpace.map n g
  let X' := AffineSpace n (Spec (.of R))
  let f' : X' ⟶ Spec (.of R) := X' ↘ Spec (.of R)
  let Z := pullback i₀ a
  let i : Z ⟶ X' := pullback.snd i₀ a
  have hi : Set.range i.base = (a ⁻¹ᵁ U : Set X')ᶜ := by
    rw [Scheme.Pullback.range_snd]
    change a ⁻¹' Set.range (Scheme.Opens.closedComplement U).base =
      (a ⁻¹' (U : Set X))ᶜ
    rw [Scheme.Opens.range_closedComplement, Set.preimage_compl]
  let gV := W.toScheme.isoSpec.inv ≫ Y.homOfLE hWV
  have hgV : gV ≫ V.ι = g := by
    dsimp [gV, g]
    rw [Category.assoc, Scheme.homOfLE_ι]
  have sqV := (IsPullback.of_hasPullback (h ∣_ V) gV).paste_horiz
    (isPullback_morphismRestrict h V).flip
  rw [hgV] at sqV
  have : IsFinite (pullback.snd h g) := by
    rw [← sqV.isoPullback_inv_snd]
    infer_instance
  have sq := (IsPullback.of_hasPullback i₀ a).paste_vert
    (AffineSpace.isPullback_map (n := n) g)
  have hif : IsFinite (i ≫ f') := by
    change IsFinite (pullback.snd i₀ a ≫
      (AffineSpace n (Spec Γ(W.toScheme, ⊤)) ↘ Spec Γ(W.toScheme, ⊤)))
    rw [← sq.isoPullback_hom_snd]
    infer_instance
  exact ⟨R, inferInstance, inferInstance, g, inferInstance, hgd,
    Z, i, inferInstance, hi, hif⟩

end AlgebraicGeometry.AffineSpace
