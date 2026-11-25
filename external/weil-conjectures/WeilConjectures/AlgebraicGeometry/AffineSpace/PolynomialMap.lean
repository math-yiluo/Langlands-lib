/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import Mathlib.FieldTheory.Perfect

/-!
# Polynomial maps of the affine line

For a field `k` and `P ∈ k[X]`, the polynomial map `x ↦ P(x)` of the affine line `𝔸¹_k`
is `AlgebraicGeometry.affineLine.polynomialMap P`, the spectrum of `k[z] ⟶ k[X]`, `z ↦ P`, read
through the identification `AlgebraicGeometry.affineLine.isoSpecPolynomial` of `𝔸¹_k` with
`Spec k[X]`. If `P` is monic of positive degree, it is finite
(`AlgebraicGeometry.affineLine.isFinite_polynomialMap`) and étale over every open whose preimage
avoids the zeros of `P'` (`AlgebraicGeometry.affineLine.etale_morphismRestrict_polynomialMap`);
the zeros of `P` are the preimage of the origin
(`AlgebraicGeometry.affineLine.polynomialMap_mem_basicOpen_iff`).
-/

@[expose] public section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry

/-- A point of `Spec R[n]` lies in the locus `xᵢ ≠ 0` of `𝔸ⁿ_R` if and only if `Xᵢ` is not in
the corresponding prime. -/
lemma AffineSpace.SpecIso_inv_mem_basicOpen_coord_iff {n : Type u} (R : CommRingCat.{u}) (i : n)
    (x : Spec (.of (MvPolynomial n R))) :
    (SpecIso n R).inv x ∈ 𝔸(n; Spec R).basicOpen (coord _ i) ↔ MvPolynomial.X i ∉ x.asIdeal := by
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top, SpecIso_inv_appTop_coord,
    basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

variable (k : Type u) [Field k]

/-- The affine line over a field `k` is the spectrum of the polynomial ring `k[X]`. -/
noncomputable def affineLine.isoSpecPolynomial : affineLine k ≅ Spec (.of k[X]) :=
  AffineSpace.SpecIso PUnit.{u + 1} (.of k) ≪≫ Scheme.Spec.mapIso
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).symm.toRingEquiv.toCommRingCatIso.op

lemma affineLine.isoSpecPolynomial_inv :
    (isoSpecPolynomial k).inv = Spec.map (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).toRingEquiv.toRingHom) ≫
        (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv := rfl

@[reassoc (attr := simp)]
lemma affineLine.isoSpecPolynomial_inv_over :
    (isoSpecPolynomial k).inv ≫ affineLine k ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom C) := by
  rw [isoSpecPolynomial_inv, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

/-- A prime of `k[X]` lies in the locus `x ≠ 0` of `𝔸¹_k` if and only if it does not contain
`X`. -/
lemma affineLine.isoSpecPolynomial_inv_mem_basicOpen_iff (x : Spec (.of k[X])) :
    (isoSpecPolynomial k).inv x ∈ (affineLine k).basicOpen
      (AffineSpace.coord (Spec (.of k)) PUnit.unit) ↔ (X : k[X]) ∉ x.asIdeal := by
  rw [isoSpecPolynomial_inv, Scheme.Hom.comp_apply,
    AffineSpace.SpecIso_inv_mem_basicOpen_coord_iff, Spec.map_apply]
  simp

variable {k}

/-- The polynomial map `x ↦ P(x)` of the affine line `𝔸¹_k`: the spectrum of the `k`-algebra
map `k[z] ⟶ k[X]`, `z ↦ P`. -/
noncomputable def affineLine.polynomialMap (P : k[X]) : affineLine k ⟶ affineLine k :=
  (isoSpecPolynomial k).hom ≫ Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := k) fun _ : PUnit.{u + 1} ↦ P).toRingHom) ≫
      (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv

@[reassoc (attr := simp)]
lemma affineLine.polynomialMap_over (P : k[X]) :
    polynomialMap P ≫ affineLine k ↘ Spec (.of k) = affineLine k ↘ Spec (.of k) := by
  rw [← cancel_epi (isoSpecPolynomial k).inv, isoSpecPolynomial_inv_over]
  simp only [polynomialMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [AffineSpace.SpecIso_inv_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

instance (P : k[X]) : (affineLine.polynomialMap P).IsOver (Spec (.of k)) :=
  ⟨affineLine.polynomialMap_over P⟩

/-- For `P` monic of positive degree, the polynomial map `x ↦ P(x)` is finite. -/
lemma affineLine.isFinite_polynomialMap {P : k[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    IsFinite (polynomialMap P) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k) fun _ : PUnit.{u + 1} ↦ P).toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr (Monic.finite_aeval_pUnit P hP hdeg)
  rw [polynomialMap]
  infer_instance

/-- The polynomial map `x ↦ P(x)` sends `x` to the origin if and only if `P` vanishes at `x`. -/
lemma affineLine.polynomialMap_mem_basicOpen_iff (P : k[X]) (x : affineLine k) :
    polynomialMap P x ∈ (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) ↔
      P ∉ ((isoSpecPolynomial k).hom x).asIdeal := by
  rw [polynomialMap, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    AffineSpace.SpecIso_inv_mem_basicOpen_coord_iff, Spec.map_apply]
  simp

/-- For `P` monic of positive degree, the polynomial map `x ↦ P(x)` is étale over every open `V`
whose preimage avoids the zeros of `P'`. -/
lemma affineLine.etale_morphismRestrict_polynomialMap {P : k[X]} (hP : P.Monic)
    (hdeg : 0 < P.natDegree) {V : (affineLine k).Opens}
    (hV : polynomialMap P ⁻¹ᵁ V ≤ (isoSpecPolynomial k).hom ⁻¹ᵁ
      PrimeSpectrum.basicOpen (R := CommRingCat.of k[X]) (derivative P)) :
    Etale (polynomialMap P ∣_ V) := by
  have := etale_basicOpen_ι_comp_SpecMap (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k) fun _ : PUnit.{u + 1} ↦ P).toRingHom)
    (derivative P : CommRingCat.of k[X]) (hP.etale_aeval_pUnit P hdeg)
  have : Etale (((isoSpecPolynomial k).hom ⁻¹ᵁ
      PrimeSpectrum.basicOpen (R := CommRingCat.of k[X]) (derivative P)).ι ≫
      polynomialMap P) := by
    rw [polynomialMap, ← Category.assoc, ← morphismRestrict_ι, Category.assoc,
      ← Category.assoc (Scheme.Opens.ι _)]
    infer_instance
  exact etale_morphismRestrict_of_le _ hV

variable (k) in
/-- The origin is a single point: the complement of the locus `x ≠ 0` of `𝔸¹_k` is finite. -/
lemma affineLine.finite_compl_basicOpen_coord :
    ((affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) :
      Set (affineLine k))ᶜ.Finite := by
  have he (x : affineLine k) : (isoSpecPolynomial k).inv ((isoSpecPolynomial k).hom x) = x := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  refine ((finite_setOf_mem_asIdeal X_ne_zero).preimage
    (isoSpecPolynomial k).hom.isOpenEmbedding.injective.injOn).subset fun x hx ↦ ?_
  by_contra hX
  refine hx ?_
  rw [← he x]
  exact (isoSpecPolynomial_inv_mem_basicOpen_iff k _).mpr hX

/-- **A finite map of `𝔸¹` which is étale near the origin and sees only a given open there.**
Let `O` be a nonempty open of the affine line over a perfect field `k`. There are a polynomial
`P` such that the polynomial map `p : x ↦ P(x)` is finite, and an open `V ∋ 0` of `𝔸¹_k` with
finite complement such that `p⁻¹(V) ⊆ O` and `p` is étale over `V`.

Proof: `O` contains a basic open `D(h)`, `h ≠ 0`; take a monic irreducible (hence separable)
`P` coprime to `h`. The bad locus `C = (𝔸¹ ∖ O) ∪ V(P')` is closed and finite, and
`V = 𝔸¹ ∖ p(C)` works: `p` is finite hence closed, and the fibre `V(P)` of `p` over `0` lies in
`D(h) ∩ D(P')`. -/
theorem affineLine.exists_isFinite_polynomialMap_etale [PerfectField k] (O : (affineLine k).Opens)
    (hO : (O : Set (affineLine k)).Nonempty) :
    ∃ P : k[X], IsFinite (polynomialMap P) ∧ ∃ V : (affineLine k).Opens,
      (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) ⊔ V = ⊤ ∧
      ((V : Set (affineLine k))ᶜ).Finite ∧ polynomialMap P ⁻¹ᵁ V ≤ O ∧
      Etale (polynomialMap P ∣_ V) := by
  set e := isoSpecPolynomial k
  have he (x : affineLine k) : e.inv (e.hom x) = x := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  -- a nonzero polynomial `h` with `D(h) ⊆ O`
  obtain ⟨h, hh0, hh⟩ : ∃ h : k[X], h ≠ 0 ∧ ∀ 𝔭 : Spec (.of k[X]), h ∉ 𝔭.asIdeal → e.inv 𝔭 ∈ O := by
    obtain ⟨x, hx⟩ := hO
    obtain ⟨_, ⟨h, rfl⟩, hxh, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := e.hom x) (by simpa [he] using hx) (O.isOpen.preimage e.inv.continuous)
    exact ⟨h, fun h0 ↦ hxh (h0 ▸ Ideal.zero_mem _), fun 𝔭 h𝔭 ↦ hsub h𝔭⟩
  -- a monic irreducible, hence separable, `P` coprime to `h`
  obtain ⟨P, hPm, hPirr, hPh⟩ := exists_monic_irreducible_isCoprime hh0
  have hPsep : IsCoprime P (derivative P) := PerfectField.separable_of_irreducible hPirr
  have hdeg : 0 < P.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hPirr)
  have hP' : derivative P ≠ 0 := fun h0 ↦
    hPirr.not_isUnit (isCoprime_zero_right.mp (h0 ▸ hPsep))
  have := isFinite_polynomialMap hPm hdeg
  set p := polynomialMap P
  -- the bad locus `C`: outside `O` or where `P'` vanishes
  set C : Set (affineLine k) := (O : Set (affineLine k))ᶜ ∪ e.hom ⁻¹' {𝔭 | derivative P ∈ 𝔭.asIdeal}
  have hZ : IsClosed {𝔭 : Spec (.of k[X]) | derivative P ∈ 𝔭.asIdeal} := by
    have := PrimeSpectrum.isClosed_zeroLocus (R := k[X]) {derivative P}
    simp only [PrimeSpectrum.zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at this
    exact this
  have hinj := e.hom.isOpenEmbedding.injective.injOn (s := Set.univ)
  have hCf : C.Finite := by
    refine Set.Finite.union (((finite_setOf_mem_asIdeal hh0).preimage
      (hinj.mono (Set.subset_univ _))).subset fun x hx ↦ by_contra fun hhx ↦ hx ?_)
      ((finite_setOf_mem_asIdeal hP').preimage (hinj.mono (Set.subset_univ _)))
    simpa [he] using hh (e.hom x) hhx
  set V : (affineLine k).Opens := ⟨(p '' C)ᶜ,
    (p.isClosedMap C (O.isOpen.isClosed_compl.union (hZ.preimage e.hom.continuous))).isOpen_compl⟩
  have hV (x : affineLine k) (hx : x ∈ p ⁻¹ᵁ V) : x ∉ C := fun hxC ↦ hx ⟨x, hxC, rfl⟩
  refine ⟨P, this, V, ?_, (hCf.image p).subset fun a ha ↦ by_contra fun h ↦ ha h,
    fun x hx ↦ by_contra fun hxO ↦ hV x hx (Or.inl hxO),
    etale_morphismRestrict_polynomialMap hPm hdeg fun x hx ↦ by_contra fun hx' ↦
      hV x hx (Or.inr (by_contra fun h' ↦ hx' ((PrimeSpectrum.mem_basicOpen _ _).mpr h')))⟩
  -- the fibre of `p` over the origin is `V(P)`, which avoids `C`
  rw [eq_top_iff]
  intro a _
  by_cases ha : a ∈ (affineLine k).basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit)
  · exact Or.inl ha
  refine Or.inr fun ⟨c, hc, hca⟩ ↦ ?_
  rw [← hca, polynomialMap_mem_basicOpen_iff, not_not] at ha
  refine hc.elim (fun hcO ↦ hcO ?_) (Ideal.IsPrime.notMem_of_isCoprime_of_mem hPsep ha)
  rw [← he c]
  exact hh _ (Ideal.IsPrime.notMem_of_isCoprime_of_mem hPh ha)

end AlgebraicGeometry
