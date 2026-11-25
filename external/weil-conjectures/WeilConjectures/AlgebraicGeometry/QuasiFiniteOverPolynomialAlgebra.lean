/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.ZariskisMainTheorem

/-! # Quasi-finite over a polynomial algebra

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00QE
(blueprint: lem-weil-pbc-quasi-finite-over-polynomial-algebra).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem isQuasiFiniteAtPrime_iff_quasiFiniteAt
    (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [FiniteType A B] (q : PrimeSpectrum B) :
    IsQuasiFiniteAtPrime A B q ↔ QuasiFiniteAt A q.asIdeal := by
  unfold IsQuasiFiniteAtPrime
  let e := PrimeSpectrum.preimageHomeomorphFiber A B (q.comap (algebraMap A B))
  have he : IsOpen ({e ⟨q, rfl⟩} : Set _) ↔
      IsOpen (X := PrimeSpectrum.comap (algebraMap A B) ⁻¹'
        {q.comap (algebraMap A B)}) {⟨q, rfl⟩} := by
    simpa only [Set.image_singleton] using (e.isOpen_image (s := {⟨q, rfl⟩}))
  exact he.trans (quasiFiniteAt_iff_isOpen_singleton_fiber q).symm

private theorem exists_away_fibre_dimension_eq
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ)
    (hdim : topologicalKrullDimAt
      (X := PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S))
      ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)))
        ⟨q, rfl⟩) = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      topologicalKrullDim
        (PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber (Localization.Away g))) =
          (n : WithBot ℕ∞) := by
  classical
  let p := q.comap (algebraMap R S)
  let F := p.asIdeal.Fiber S
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  let Q : PrimeSpectrum F := e ⟨q, rfl⟩
  let j := PrimeSpectrum.comap (TensorProduct.includeRight (R := R)
    (A := p.asIdeal.ResidueField) (B := S)).toRingHom
  have hj : Topology.IsEmbedding j := by
    convert Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding using 1
    rfl
  have hQ : j Q = q := congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
  let N := {U : TopologicalSpace.Opens (PrimeSpectrum F) // Q ∈ U}
  let : Nonempty N := ⟨⟨⊤, trivial⟩⟩
  obtain ⟨U, hU⟩ := ciInf_mem (fun V : N ↦ topologicalKrullDim V.1)
  have hmin : topologicalKrullDim U.1 = (n : WithBot ℕ∞) := by
    calc
      topologicalKrullDim U.1 = topologicalKrullDimAt Q := by
        simpa [topologicalKrullDimAt, N, iInf_subtype] using hU
      _ = n := hdim
  obtain ⟨V, hV, hUV⟩ := hj.isInducing.isOpen_iff.mp U.1.isOpen
  have hqV : q ∈ V := by
    have hQU : Q ∈ (U.1 : Set (PrimeSpectrum F)) := U.2
    rw [← hUV] at hQU
    rwa [Set.mem_preimage, hQ] at hQU
  obtain ⟨_, ⟨g, rfl⟩, hqg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hV
  let a : F := TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField) g
  have hQa : Q ∈ PrimeSpectrum.basicOpen a := by
    change g ∉ (j Q).asIdeal
    rwa [hQ]
  have hsub : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum F)) ⊆ U.1 := by
    intro x hx
    rw [← hUV]
    exact hgV hx
  have hbasic : topologicalKrullDim (PrimeSpectrum.basicOpen a) = (n : WithBot ℕ∞) := by
    apply le_antisymm
    · exact ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans
        hmin.le
    · rw [← hdim]
      exact iInf₂_le (PrimeSpectrum.basicOpen a) hQa
  let E := PrimeSpectrum.homeomorphOfRingEquiv
    (IsLocalization.Away.tensorProductEquivTMulRight R p.asIdeal.ResidueField g
      (Localization.Away g)).toRingEquiv
  let L := Localization.Away a
  have he := PrimeSpectrum.localization_away_isOpenEmbedding L a
  have hr := PrimeSpectrum.localization_away_comap_range L a
  let H := he.isEmbedding.toHomeomorph
  have heq := H.isHomeomorph.topologicalKrullDim_eq H
  rw [hr] at heq
  refine ⟨g, hqg, ?_⟩
  exact (E.isHomeomorph.topologicalKrullDim_eq E).trans (heq.trans hbasic)

private theorem isOpen_singleton_fiber_of_embedding
    {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (a : X → Y) (b : X' → Y') (i : X' → X) (j : Y' → Y)
    (hi : Topology.IsEmbedding i) (hj : Function.Injective j)
    (hsq : ∀ x, a (i x) = j (b x)) (x : X')
    (hcover : ∀ y : X, a y = a (i x) → ∃ z : X', i z = y)
    (ho : IsOpen (X := b ⁻¹' {b x}) {⟨x, rfl⟩}) :
    IsOpen (X := a ⁻¹' {a (i x)}) {⟨i x, rfl⟩} := by
  let A := a ⁻¹' {a (i x)}
  let B := b ⁻¹' {b x}
  have hB : B = i ⁻¹' A := by
    ext z
    change b z = b x ↔ a (i z) = a (i x)
    rw [hsq z, hsq x]
    exact hj.eq_iff.symm
  let e := Homeomorph.setCongr hB
  let k : B → A := (A.restrictPreimage i) ∘ e
  have hk : Topology.IsEmbedding k := (hi.restrictPreimage A).comp e.isEmbedding
  have hs : Function.Surjective k := by
    intro y
    obtain ⟨z, hz⟩ := hcover y.1 y.2
    have hzB : z ∈ B := by
      rw [hB]
      change i z ∈ A
      rw [hz]
      exact y.2
    exact ⟨⟨z, hzB⟩, Subtype.ext hz⟩
  let H := hk.toHomeomorphOfSurjective hs
  have hx : H ⟨x, rfl⟩ = ⟨i x, rfl⟩ := by rfl
  simpa only [Set.image_singleton, hx] using H.isOpenMap _ ho

/-- If the entire fibre at the contraction of `q` has dimension `n`, polynomial
coordinates in `n` variables can be chosen so that the map is quasi-finite at `q`.
Source: Stacks Project, Algebra, Lemma Tag 00QE, second paragraph of the proof,
using Noether normalization Tag 00OY.
(blueprint: lem-weil-pbc-quasi-finite-over-polynomial-algebra).

Proof: Put `p = q ∩ R`, `k = κ(p)` and `F = k ⊗[R] S`. The fibre contains the point
corresponding to `q`, so it is nonzero. It is finite type over `k` by base change.
The dimension of its spectrum equals its ring Krull dimension. Noether normalization
therefore supplies an injective finite map `k[t₁, …, t_n] → F`. For each variable
image `y_i`, the localization-quotient presentation of `F` gives `u_i ∉ p` and
`s_i ∈ S` with `u_i y_i = 1 ⊗ s_i`. Multiplication of each variable by the nonzero
scalar `u_i` is a polynomial automorphism over `k`, so the rescaled coordinate map
is still finite. Set `f = aeval s`. Its base change is this finite coordinate map.
Polynomial scalar extension identifies `k ⊗[R] R[t]` with `k[t]` and hence
makes `F` finite over `k ⊗[R] R[t]`. The commuting square on spectra has fibre
embeddings as its vertical maps. Every point in the fibre through `q` contracts
to `p`, so this fibre is homeomorphic to the fibre through the point of `Spec F`.
The finite map upstairs is quasi-finite, and its distinguished singleton is open.
Transport that open singleton to obtain the required quasi-finiteness at `q`.
Finally the original finite set of generators over `R` also generates `S` over
`R[t]`, because the structure map extends the original `R`-algebra structure. -/
private theorem exists_polynomial_isQuasiFiniteAtPrime_of_fibre_dimension
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (n : ℕ)
    (hdim : topologicalKrullDim
      (PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S)) = (n : WithBot ℕ∞)) :
    ∃ (f : MvPolynomial (Fin n) R →ₐ[R] S)
      (hft : @Algebra.FiniteType (MvPolynomial (Fin n) R) S _ _ f.toRingHom.toAlgebra),
      @Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) R) S
        _ _ f.toRingHom.toAlgebra hft q := by
  classical
  let p := q.comap (algebraMap R S)
  let k := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  let : Algebra S F := TensorProduct.rightAlgebra
  let Q : PrimeSpectrum F := PrimeSpectrum.preimageHomeomorphFiber R S p ⟨q, rfl⟩
  have : Nontrivial F := Q.nontrivial
  have hd : ringKrullDim F = (n : WithBot ℕ∞) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdim
  obtain ⟨g, _, hfin⟩ := exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq k F n hd
  have hlift (i : Fin n) : ∃ u ∉ p.asIdeal, ∃ s : S,
      u • g (MvPolynomial.X i) = _root_.TensorProduct.tmul R (1 : k) s :=
    Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal (g (MvPolynomial.X i))
  choose u hu s hs using hlift
  let v : Fin n → kˣ := fun i ↦ Units.mk0 (algebraMap R k (u i)) (by
    exact fun h ↦ hu i (by
      rwa [Ideal.algebraMap_residueField_eq_zero] at h))
  have hresc (w : Fin n → kˣ) :
      (MvPolynomial.aeval (R := k) fun i ↦ MvPolynomial.C (w i : k) * MvPolynomial.X i).comp
        (MvPolynomial.aeval fun i ↦ MvPolynomial.C (↑(w i)⁻¹ : k) * MvPolynomial.X i) =
      AlgHom.id k _ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul,
      Units.inv_mul, map_one, one_mul, AlgHom.id_apply]
  have hv : Function.Bijective
      (MvPolynomial.aeval (R := k) fun i ↦ MvPolynomial.C (v i : k) * MvPolynomial.X i) :=
    ⟨Function.LeftInverse.injective
      (g := MvPolynomial.aeval fun i ↦ MvPolynomial.C (↑(v i)⁻¹ : k) * MvPolynomial.X i)
      fun t ↦ by simpa using congr($(hresc fun i ↦ (v i)⁻¹) t),
    Function.RightInverse.surjective
      (g := MvPolynomial.aeval fun i ↦ MvPolynomial.C (↑(v i)⁻¹ : k) * MvPolynomial.X i)
      fun t ↦ by simpa using congr($(hresc v) t)⟩
  let g' := g.comp (MvPolynomial.aeval fun i ↦
    MvPolynomial.C (v i : k) * MvPolynomial.X i)
  have hg'X (i : Fin n) : g' (MvPolynomial.X i) =
      TensorProduct.includeRight (R := R) (A := k) (s i) := by
    simp only [g', AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul]
    rw [← MvPolynomial.algebraMap_eq, g.commutes]
    change algebraMap k F (algebraMap R k (u i)) * g (MvPolynomial.X i) = _
    rw [← IsScalarTower.algebraMap_apply R k F, ← Algebra.smul_def]
    exact hs i
  have hg'fin : g'.Finite := RingHom.Finite.comp hfin
    (RingHom.Finite.of_surjective _ hv.surjective)
  let f : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval s
  let : Algebra (MvPolynomial (Fin n) R) S := f.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have hft : FiniteType (MvPolynomial (Fin n) R) S :=
    FiniteType.of_restrictScalars_finiteType R _ _
  let A := MvPolynomial (Fin n) R
  let Ak := p.asIdeal.Fiber A
  let ep : Ak ≃ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.algebraTensorAlgEquiv R k
  let G := g'.comp ep.toAlgHom
  have hGfin : G.Finite := RingHom.Finite.comp hg'fin
    (RingHom.Finite.of_surjective _ ep.surjective)
  have hcomp : g'.toRingHom.comp (MvPolynomial.map (algebraMap R k)) =
      TensorProduct.includeRight.toRingHom.comp f.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      change g' (MvPolynomial.C (algebraMap R k r)) = TensorProduct.includeRight
        (f (MvPolynomial.C r))
      rw [← MvPolynomial.algebraMap_eq, g'.commutes]
      rw [show f (MvPolynomial.C r) = algebraMap R S r from f.commutes r]
      exact (IsScalarTower.algebraMap_apply R k F r).symm.trans
        (IsScalarTower.algebraMap_apply R S F r)
    · simp only [RingHom.comp_apply, MvPolynomial.map_X]
      change g' (MvPolynomial.X i) = TensorProduct.includeRight (f (MvPolynomial.X i))
      simpa only [f, MvPolynomial.aeval_X] using hg'X i
  have hG (a : A) : G (TensorProduct.includeRight (R := R) (A := k) a) =
      TensorProduct.includeRight (R := R) (A := k) (f a) := by
    change g' (ep (_root_.TensorProduct.tmul R (1 : k) a)) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    exact RingHom.congr_fun hcomp a
  let : Algebra Ak F := G.toRingHom.toAlgebra
  have : Module.Finite Ak F := hGfin
  have : FiniteType Ak F := inferInstance
  let i := PrimeSpectrum.comap (TensorProduct.includeRight (R := R) (A := k)
    (B := S)).toRingHom
  let j := PrimeSpectrum.comap (TensorProduct.includeRight (R := R) (A := k)
    (B := A)).toRingHom
  let eS := PrimeSpectrum.preimageHomeomorphFiber R S p
  let eA := PrimeSpectrum.preimageHomeomorphFiber R A p
  have hi : Topology.IsEmbedding i := by
    convert Topology.IsEmbedding.subtypeVal.comp eS.symm.isEmbedding using 1
    rfl
  have hj : Function.Injective j := by
    have he : Topology.IsEmbedding j := by
      convert Topology.IsEmbedding.subtypeVal.comp eA.symm.isEmbedding using 1
      rfl
    exact he.injective
  have hsq (x : PrimeSpectrum F) :
      (i x).comap f.toRingHom = j (x.comap G.toRingHom) := by
    apply PrimeSpectrum.ext
    ext a
    change TensorProduct.includeRight (f a) ∈ x.asIdeal ↔
      G (TensorProduct.includeRight a) ∈ x.asIdeal
    rw [hG]
  have hQ : i Q = q := congrArg Subtype.val (eS.symm_apply_apply ⟨q, rfl⟩)
  have ho : IsOpen (X := PrimeSpectrum.comap f.toRingHom ⁻¹' {q.comap f.toRingHom})
      {⟨q, rfl⟩} := by
    rw [← hQ]
    apply isOpen_singleton_fiber_of_embedding
      (PrimeSpectrum.comap f.toRingHom) (PrimeSpectrum.comap G.toRingHom) i j hi hj hsq Q
    · intro q' hq'
      have hq'R : q'.comap (algebraMap R S) = p := by
        have h := congrArg (PrimeSpectrum.comap (algebraMap R A)) hq'
        have hfR : f.toRingHom.comp (algebraMap R A) = algebraMap R S :=
          RingHom.ext f.commutes
        rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
          hfR, hQ] at h
        exact h
      refine ⟨eS ⟨q', hq'R⟩, ?_⟩
      exact congrArg Subtype.val (eS.symm_apply_apply ⟨q', hq'R⟩)
    · exact (quasiFiniteAt_iff_isOpen_singleton_fiber Q).mp inferInstance
  refine ⟨f, hft, ?_⟩
  unfold IsQuasiFiniteAtPrime
  let E := PrimeSpectrum.preimageHomeomorphFiber A S (q.comap f.toRingHom)
  change IsOpen ({E ⟨q, rfl⟩} : Set _)
  simpa only [Set.image_singleton] using E.isOpenMap _ ho

set_option linter.unusedVariables false in
/-- A finite type algebra is locally quasi-finite over a polynomial algebra in its fibre
 dimension.

Source: Stacks Project, Algebra, Lemma Tag 00QE
(blueprint: lem-weil-pbc-quasi-finite-over-polynomial-algebra).
Proof:

1. Put `p = q ∩ R` and `F = κ(p) ⊗[R] S`. The fibre homeomorphism embeds
`Spec F` in `Spec S`. The infimum of dimensions of open neighbourhoods of the
point corresponding to `q` is attained. Pull an ambient basic open `D(g₀)` back
into a minimizing neighbourhood. Monotonicity and the defining infimum force
its dimension to be `n`. Localization and base change identify this open with
`Spec (κ(p) ⊗[R] S[g₀⁻¹])`. Lift `q` to the localized prime `q₀`.

2. Noether normalization gives a finite map from `κ(p)[t₁, …, t_n]` to this
localized fibre. Write each variable image as `yᵢ`, and clear its residue-field
denominator: `uᵢ • yᵢ = 1 ⊗ sᵢ`, with `uᵢ ∉ p` and `sᵢ ∈ S[g₀⁻¹]`.
Scaling each variable by the unit `uᵢ` is a polynomial automorphism, so the
rescaled map remains finite. The elements `sᵢ` define the required coordinate
map `f₀ : R[t₁, …, t_n] → S[g₀⁻¹]`, initially at `q₀`.

3. Polynomial scalar extension and the rescaled normalization give a finite
map on the `κ(p)`-fibres. The fibre embeddings form a commuting square on
spectra. Every point in the fibre of `f₀` through `q₀` lies over `p` and lifts
upstairs, so restricting the embedding gives a homeomorphism of the whole
fibres. The finite map upstairs has an open singleton at the distinguished
point. Transporting it proves quasi-finiteness at `q₀`. Restricting scalars
from the original finite-type algebra gives finite type over the polynomial ring.

4. Mathlib's finite-subalgebra form of Zariski's Main Theorem supplies a finite
polynomial subalgebra and an element `h ∉ q₀` whose localizations map bijectively
onto `S[g₀⁻¹][h⁻¹]`. Finiteness, localization, and this surjection give
quasi-finiteness at every prime of the latter ring. Let `b` be a numerator of `h`;
its image is associated to `h`, so `b ∉ q`. The iterated localization is a
localization of `S` away from `g₀*b`. Transport `f₀` and quasi-finiteness across
its canonical algebra equivalence with `S[(g₀*b)⁻¹]`. -/
theorem exists_quasiFinite_over_polynomial_algebra
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (n : ℕ)
    (hdim : topologicalKrullDimAt
      (X := PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S))
      ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)))
        ⟨q, rfl⟩) = (n : WithBot ℕ∞)) :
    ∃ (g : S) (hg : g ∉ q.asIdeal)
      (f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g)
      (hft : @Algebra.FiniteType (MvPolynomial (Fin n) R) (Localization.Away g)
        _ _ f.toRingHom.toAlgebra),
      ∀ (q' : PrimeSpectrum (Localization.Away g)),
        @Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) R) (Localization.Away g)
          _ _ f.toRingHom.toAlgebra hft q' := by
  classical
  obtain ⟨g₀, hg₀, hdim₀⟩ := exists_away_fibre_dimension_eq R S q n hdim
  let S₀ := Localization.Away g₀
  obtain ⟨q₀, hq₀⟩ :=
    (PrimeSpectrum.localization_away_comap_range S₀ g₀).ge hg₀
  have hp₀ : q₀.comap (algebraMap R S₀) = q.comap (algebraMap R S) := by
    rw [IsScalarTower.algebraMap_eq R S S₀, PrimeSpectrum.comap_comp_apply, hq₀]
  have hd : topologicalKrullDim
      (PrimeSpectrum ((q₀.comap (algebraMap R S₀)).asIdeal.Fiber S₀)) =
        (n : WithBot ℕ∞) := by
    rw [hp₀]
    exact hdim₀
  obtain ⟨f₀, hft₀, hqf₀⟩ :=
    exists_polynomial_isQuasiFiniteAtPrime_of_fibre_dimension R S₀ q₀ n hd
  let A := MvPolynomial (Fin n) R
  let : Algebra A S₀ := f₀.toRingHom.toAlgebra
  let : FiniteType A S₀ := hft₀
  let : IsScalarTower R A S₀ := .of_algebraMap_eq fun r ↦ (f₀.commutes r).symm
  let : QuasiFiniteAt A q₀.asIdeal :=
    (isQuasiFiniteAtPrime_iff_quasiFiniteAt A S₀ q₀).mp hqf₀
  obtain ⟨S', hS', r, hh, hr⟩ :=
    QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q₀.asIdeal
  let h : S₀ := r.1
  have : Module.Finite A S' := Module.Finite.iff_fg.mpr hS'
  have : QuasiFinite A (Localization.Away r) := inferInstance
  have : QuasiFinite A (Localization.Away h) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) hr.2
  have hquasi (qT : PrimeSpectrum (Localization.Away h)) :
      IsQuasiFiniteAtPrime A (Localization.Away h) qT :=
    (isQuasiFiniteAtPrime_iff_quasiFiniteAt A _ qT).mpr inferInstance
  let b := (IsLocalization.Away.sec g₀ h).1
  have hb : b ∉ q.asIdeal := by
    intro hb
    have hb₀ : algebraMap S S₀ b ∈ q₀.asIdeal := by
      change b ∈ (q₀.comap (algebraMap S S₀)).asIdeal
      rwa [hq₀]
    exact hh ((q₀.asIdeal.mem_iff_of_associated
      (IsLocalization.Away.associated_sec_fst g₀ h)).mp hb₀)
  let T := Localization.Away h
  let : IsLocalization.Away (g₀ * b) T :=
    IsLocalization.Away.mul_of_associated g₀ b h
      (IsLocalization.Away.associated_sec_fst g₀ h)
  let e : T ≃ₐ[S] Localization.Away (g₀ * b) :=
    IsLocalization.algEquiv (Submonoid.powers (g₀ * b)) T (Localization.Away (g₀ * b))
  let f : A →ₐ[R] Localization.Away (g₀ * b) :=
    (e.toAlgHom.restrictScalars R).comp (IsScalarTower.toAlgHom R S₀ T |>.comp f₀)
  let : Algebra A (Localization.Away (g₀ * b)) := f.toRingHom.toAlgebra
  let : IsScalarTower R A (Localization.Away (g₀ * b)) :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have hft : FiniteType A (Localization.Away (g₀ * b)) :=
    FiniteType.of_restrictScalars_finiteType R A _
  refine ⟨g₀ * b, q.isPrime.mul_notMem hg₀ hb, f, hft, ?_⟩
  intro q'
  let eA : T ≃ₐ[A] Localization.Away (g₀ * b) :=
    { e.toRingEquiv with commutes' := fun a ↦ rfl }
  let qT := q'.comap eA.toRingHom
  let : QuasiFiniteAt A qT.asIdeal :=
    (isQuasiFiniteAtPrime_iff_quasiFiniteAt A T qT).mp (hquasi qT)
  let : QuasiFiniteAt A q'.asIdeal :=
    QuasiFiniteAt.of_surjectiveOnStalks qT.asIdeal eA.toAlgHom
      (RingHom.surjectiveOnStalks_of_surjective eA.surjective) q'.asIdeal rfl
  exact (isQuasiFiniteAtPrime_iff_quasiFiniteAt A _ q').mpr inferInstance

end Algebra
