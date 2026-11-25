/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.TensorProduct.Quotient
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.RingTheory.BertiniCurve

/-!
# Auxiliary results for the Bertini argument

Glue between the ring-level Bertini theorem and the geometric fiber of an affine scheme over a
finite field (blueprint `lemma-curve-preserving-finite-cover--1`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.geometricFiberIsoSpec`: for `X₀ ≅ Spec R` over `Spec k`, the
  identification `X₀ ×_k k̄ ≅ Spec (k̄ ⊗[k] R)`.
- `AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberIsoSpec_hom`:
  under it, the geometric Galois Frobenius acts as `σ ⊗ 𝟙`
  (`AlgebraicGeometry.geometricFrobeniusTensor`).
- `AlgebraicGeometry.exists_geometricFrobeniusTensor_pow_apply_eq_self`: every element of
  `k̄ ⊗[k] R` is fixed by a positive power of `σ ⊗ 𝟙`.
- `Ideal.FG.exists_map_pow_eq`: a finitely generated ideal is then stable under a positive power.
- `AlgebraicGeometry.exists_iso_comp_eq_of_map_eq`: a stable ideal gives an automorphism of the
  closed subscheme compatible with the automorphism of the ambient scheme.
- `AlgebraicGeometry.exists_ideal_smoothOfRelativeDimension_one_connectedSpace_pullback`: the
  ring-level Bertini theorem phrased with affine schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Module

/-- A finite flat module over a domain has rank `finrank` at every prime. -/
theorem rankAtStalk_eq_finrank_of_isDomain {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (p : PrimeSpectrum R) :
    rankAtStalk M p = finrank R M := by
  rw [← p.asIdeal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]

end Module

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Over a domain, an algebra is locally standard smooth of relative dimension `n` if and only if
it is smooth and its Kähler differentials have rank `n`. -/
theorem locally_isStandardSmoothOfRelativeDimension_iff_rank [IsDomain S] (n : ℕ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S) ↔
      Smooth R S ∧ Module.rank S Ω[S⁄R] = n := by
  rw [locally_isStandardSmoothOfRelativeDimension_iff]
  refine and_congr_right fun hsm ↦ ?_
  simp_rw [Module.rankAtStalk_eq_finrank_of_isDomain, ← Module.finrank_eq_rank]
  exact ⟨fun h ↦ by rw [h ⊥], fun h _ ↦ by exact_mod_cast h⟩

end Algebra

namespace Ideal

/-- If every element is fixed by a positive power of an automorphism `σ`, then every finitely
generated ideal is stable under a positive power of `σ`. -/
theorem FG.exists_map_pow_eq {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    (σ : A ≃ₐ[R] A) (hσ : ∀ x, ∃ n, 0 < n ∧ (σ ^ n) x = x) {J : Ideal A} (hJ : J.FG) :
    ∃ m, 0 < m ∧ J.map (σ ^ m) = J := by
  classical
  obtain ⟨G, rfl⟩ := hJ
  choose n hn hfix using hσ
  refine ⟨∏ g ∈ G, n g, Finset.prod_pos fun g _ ↦ hn g, ?_⟩
  rw [Ideal.map_span]
  congr 1
  refine Set.EqOn.image_eq_self fun g hg ↦ ?_
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hg
  rw [hc, pow_mul, AlgEquiv.coe_pow]
  exact Function.IsFixedPt.iterate (hfix g) c

end Ideal

namespace Algebra.TensorProduct

variable {k K R : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K] [CommSemiring R]
  [Algebra k R]

/-- The powers of `τ ⊗ 𝟙` act on pure tensors through the powers of `τ`. -/
theorem congr_refl_pow_tmul (τ : K ≃ₐ[k] K) (n : ℕ) (a : K) (r : R) :
    (congr τ (AlgEquiv.refl : R ≃ₐ[k] R) ^ n) (a ⊗ₜ r) = (τ ^ n) a ⊗ₜ r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, congr_apply, map_tmul, pow_succ']; rfl

/-- If every element of `K` is fixed by a positive power of `τ`, then every element of `K ⊗ R`
is fixed by a positive power of `τ ⊗ 𝟙`. -/
theorem exists_congr_refl_pow_apply_eq_self (τ : K ≃ₐ[k] K)
    (hτ : ∀ x, ∃ n, 0 < n ∧ (τ ^ n) x = x) (x : K ⊗[k] R) :
    ∃ n, 0 < n ∧ (congr τ (AlgEquiv.refl : R ≃ₐ[k] R) ^ n) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
    obtain ⟨n, hn, h⟩ := hτ a
    exact ⟨n, hn, by rw [congr_refl_pow_tmul, h]⟩
  | add x y hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [map_add, pow_mul, AlgEquiv.coe_pow, Function.IsFixedPt.iterate hx, ← AlgEquiv.coe_pow,
      ← pow_mul, mul_comm, pow_mul, AlgEquiv.coe_pow, Function.IsFixedPt.iterate hy]

end Algebra.TensorProduct

namespace FiniteField

/-- Every element of the algebraic closure of a finite field is fixed by a positive power of the
geometric Frobenius. -/
theorem exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq_self (K L : Type*) [Field K]
    [Fintype K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    ∃ n, 0 < n ∧ (geometricFrobeniusAlgEquivOfAlgebraic K L ^ n) x = x := by
  obtain ⟨n, hn, h⟩ := exists_pow_card_pow_eq_self K L x
  refine ⟨n, hn, ?_⟩
  rw [geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  exact h.symm

end FiniteField

namespace AlgebraicGeometry

/-- A scheme isomorphic to a connected scheme is connected. -/
theorem Scheme.connectedSpace_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [ConnectedSpace X] :
    ConnectedSpace Y :=
  (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous

/-- `Spec S ⟶ Spec R`, for a domain `S`, is smooth of relative dimension `n` if and only if `S` is
smooth over `R` with Kähler differentials of rank `n`. -/
theorem smoothOfRelativeDimension_Spec_map_algebraMap_iff {R S : Type u} [CommRing R]
    [CommRing S] [IsDomain S] [Algebra R S] (n : ℕ) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
      Algebra.Smooth R S ∧ Module.rank S Ω[S⁄R] = n := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  exact Algebra.locally_isStandardSmoothOfRelativeDimension_iff_rank n

/-- The pullback of `Spec B ⟶ Spec A` along the closed immersion `Spec (A ⧸ J) ⟶ Spec A` is
connected if `Spec (B ⧸ J B)` is. -/
theorem connectedSpace_pullback_Spec_quotient {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (J : Ideal A) [ConnectedSpace (PrimeSpectrum (B ⧸ J.map (algebraMap A B)))] :
    ConnectedSpace ↑(pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J))))) :=
  @Scheme.connectedSpace_of_iso _ _ ((Scheme.Spec.mapIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toRingEquiv.toCommRingCatIso.op).symm ≪≫
      (pullbackSpecIso A B (A ⧸ J)).symm) ‹_›

/-- Ring-level Bertini theorem in the language of affine schemes: a smooth connected affine
scheme `Spec A` of dimension `d ≥ 2` over an algebraically closed field `K`, with a connected
finite étale cover `Spec B`, contains a smooth connected curve `Spec (A ⧸ J)` through finitely
many given `K`-points over which the cover stays connected. -/
theorem exists_ideal_smoothOfRelativeDimension_one_connectedSpace_pullback {K A B : Type u}
    [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A] [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [Algebra.Etale A B] [Module.Finite A B]
    [ConnectedSpace (PrimeSpectrum A)] [ConnectedSpace (PrimeSpectrum B)] {d : ℕ} (hd : 2 ≤ d)
    (hA : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K A))))
    (S : Set (A →+* K)) (hS : S.Finite) (hSne : S.Nonempty)
    (hS' : ∀ s ∈ S, s.comp (algebraMap K A) = RingHom.id K) :
    ∃ J : Ideal A, J.FG ∧ (∀ s ∈ S, J ≤ RingHom.ker s) ∧ IsDomain (A ⧸ J) ∧
      SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap K (A ⧸ J)))) ∧
      ConnectedSpace ↑(pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d),
    CommRingCat.hom_ofHom, Algebra.locally_isStandardSmoothOfRelativeDimension_iff] at hA
  obtain ⟨hsm, hrk⟩ := hA
  have : IsDomain A := Algebra.Smooth.isDomain_of_connectedSpace (k := K)
  have hrank : Module.rank A Ω[A⁄K] = d := by
    rw [← Module.finrank_eq_rank, ← Module.rankAtStalk_eq_finrank_of_isDomain ⊥, hrk]
  have hmax (s : A →+* K) (hs : s.comp (algebraMap K A) = RingHom.id K) :
      (RingHom.ker s).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective s fun x ↦ ⟨algebraMap K A x, congr($hs x)⟩
  obtain ⟨J, hJfg, hJS, hdom, hsmJ, hrkJ, hconn⟩ :=
    Algebra.Smooth.exists_quotient_curve_connectedSpace (B := B) hd hrank
      ((RingHom.ker ·) '' S) (hS.image _) (by rintro _ ⟨s, hs, rfl⟩; exact hmax s (hS' s hs))
      (hSne.image _)
  exact ⟨J, hJfg, fun s hs ↦ hJS _ ⟨s, hs, rfl⟩, hdom,
    (smoothOfRelativeDimension_Spec_map_algebraMap_iff 1).mpr ⟨hsmJ, hrkJ⟩,
    connectedSpace_pullback_Spec_quotient J⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

open CommRingCat

/-- An affine scheme over `Spec k` is isomorphic over `Spec k` to the spectrum of a
`k`-algebra. -/
theorem exists_iso_Spec_of_isAffine {k : Type u} [CommRing k] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of k)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R) (e : X ≅ Spec (.of R)),
      e.hom ≫ Spec.map (ofHom (algebraMap k R)) = f := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  refine ⟨Γ(X, ⊤), inferInstance, this, X.isoSpec, ?_⟩
  rw [Scheme.isoSpec_hom, RingHom.algebraMap_toAlgebra, ofHom_hom, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- `Spec (K ⊗[k] R)` is the fibre product of `Spec K` and `Spec R` over `Spec k`. -/
theorem isPullback_Spec_tensorProduct (k K R : Type u) [CommRing k] [CommRing K] [Algebra k K]
    [CommRing R] [Algebra k R] :
    IsPullback (Spec.map (ofHom (algebraMap K (K ⊗[k] R))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom))
      (Spec.map (ofHom (algebraMap k K))) (Spec.map (ofHom (algebraMap k R))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k K R)

namespace Scheme.Hom

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) {R : Type u}
  [CommRing R] [Algebra k R] (eR : X₀ ≅ Spec (.of R))
  (heR : eR.hom ≫ Spec.map (ofHom (algebraMap k R)) = f)

/-- For `X₀ ≅ Spec R` over `Spec k`, the geometric fiber is the fibre product of `Spec k̄` and
`Spec R` over `Spec k`. -/
theorem isPullback_geometricFiber_Spec (heR : eR.hom ≫ Spec.map (ofHom (algebraMap k R)) = f) :
    IsPullback f.geometricFiberToAlgebraicClosure (f.geometricFiberProj ≫ eR.hom)
      (Spec.map (ofHom (algebraMap k (AlgebraicClosure k))))
      (Spec.map (ofHom (algebraMap k R))) := by
  have h := (IsPullback.of_hasPullback f (Scheme.specAlgebraicClosure k).hom).paste_horiz
    (IsPullback.of_horiz_isIso (snd := f) (g := 𝟙 _) (f := Spec.map (ofHom (algebraMap k R)))
      (fst := eR.hom) ⟨by rw [heR, Category.comp_id]⟩)
  rw [Category.comp_id] at h
  exact h.flip

/-- The isomorphism `X₀ ×_k k̄ ≅ Spec (k̄ ⊗[k] R)` for `X₀ ≅ Spec R` over `Spec k`. -/
noncomputable def geometricFiberIsoSpec :
    f.geometricFiber ≅ Spec (.of (AlgebraicClosure k ⊗[k] R)) :=
  (isPullback_geometricFiber_Spec f eR heR).isoIsPullback _ _
    (isPullback_Spec_tensorProduct k (AlgebraicClosure k) R)

@[reassoc (attr := simp)]
theorem geometricFiberIsoSpec_hom_algebraMap :
    (geometricFiberIsoSpec f eR heR).hom ≫
        Spec.map (ofHom (algebraMap (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] R))) =
      f.geometricFiberToAlgebraicClosure :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc (attr := simp)]
theorem geometricFiberIsoSpec_hom_includeRight :
    (geometricFiberIsoSpec f eR heR).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeRight :
          R →ₐ[k] AlgebraicClosure k ⊗[k] R).toRingHom) =
      f.geometricFiberProj ≫ eR.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end Scheme.Hom

end AlgebraicGeometry

namespace AlgebraicGeometry

open CommRingCat

/-- The automorphism `σ ⊗ 𝟙` of `k̄ ⊗[k] R` induced by the geometric Frobenius `σ` of the
algebraic closure `k̄` of a finite field `k`. Under `Scheme.Hom.geometricFiberIsoSpec`, it is the
action of the geometric Galois Frobenius on the global sections of the geometric fiber
(`Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberIsoSpec_hom`). -/
noncomputable def geometricFrobeniusTensor (k R : Type u) [Field k] [Fintype k] [CommRing R]
    [Algebra k R] : (AlgebraicClosure k ⊗[k] R) ≃ₐ[k] (AlgebraicClosure k ⊗[k] R) :=
  Algebra.TensorProduct.congr (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k _)
    AlgEquiv.refl

/-- Every element of `k̄ ⊗[k] R` is fixed by a positive power of `σ ⊗ 𝟙`: it is a finite sum of
pure tensors whose `k̄`-components lie in a finite subfield of `k̄`. -/
theorem exists_geometricFrobeniusTensor_pow_apply_eq_self (k R : Type u) [Field k] [Fintype k]
    [CommRing R] [Algebra k R] (x : AlgebraicClosure k ⊗[k] R) :
    ∃ n, 0 < n ∧ (geometricFrobeniusTensor k R ^ n) x = x :=
  Algebra.TensorProduct.exists_congr_refl_pow_apply_eq_self _
    (FiniteField.exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq_self k _) x

/-- A closed subscheme `Spec (A ⧸ J)` of a scheme `X ≅ Spec A` is stable under an automorphism
`g` of `X` acting on `A` through `τ`, as soon as `τ (J) = J`: there is an automorphism `φ` of
`Spec (A ⧸ J)` with `φ ≫ i = i ≫ g`. -/
theorem exists_iso_comp_eq_of_map_eq {X : Scheme.{u}} {R' A : Type u} [CommRing R'] [CommRing A]
    [Algebra R' A] (e : X ≅ Spec (.of A)) (g : X ≅ X) (τ : A ≃ₐ[R'] A)
    (hg : g.hom ≫ e.hom = e.hom ≫ Spec.map (ofHom τ.toRingHom)) (J : Ideal A)
    (hJ : J.map τ = J) :
    ∃ φ : Spec (.of (A ⧸ J)) ≅ Spec (.of (A ⧸ J)),
      φ.hom ≫ Spec.map (ofHom (Ideal.Quotient.mk J)) ≫ e.inv =
        (Spec.map (ofHom (Ideal.Quotient.mk J)) ≫ e.inv) ≫ g.hom := by
  let q : A ⧸ J ≃+* A ⧸ J := Ideal.quotientEquiv J J τ.toRingEquiv hJ.symm
  have hq : ofHom (Ideal.Quotient.mk J) ≫ q.toCommRingCatIso.hom =
      ofHom τ.toRingHom ≫ ofHom (Ideal.Quotient.mk J) := by
    ext x
    simp [q]
  have hg' : e.inv ≫ g.hom = Spec.map (ofHom τ.toRingHom) ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hg, Iso.hom_inv_id, Category.comp_id]
  refine ⟨asIso (Spec.map q.toCommRingCatIso.hom), ?_⟩
  rw [asIso_hom, Category.assoc, hg', ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hq]

namespace Scheme.Hom

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) {R : Type u}
  [CommRing R] [Algebra k R] (eR : X₀ ≅ Spec (.of R))
  (heR : eR.hom ≫ Spec.map (ofHom (algebraMap k R)) = f)

/-- Under `X₀ ×_k k̄ ≅ Spec (k̄ ⊗[k] R)`, the geometric Galois Frobenius `𝟙 × σ` of the geometric
fiber acts on global sections as `σ ⊗ 𝟙`. -/
theorem geometricGaloisFrobenius_hom_comp_geometricFiberIsoSpec_hom [Fintype k] :
    f.geometricGaloisFrobenius.asIso.hom ≫ (geometricFiberIsoSpec f eR heR).hom =
      (geometricFiberIsoSpec f eR heR).hom ≫
        Spec.map (ofHom (geometricFrobeniusTensor k R).toRingHom) := by
  refine (isPullback_Spec_tensorProduct k (AlgebraicClosure k) R).hom_ext ?_ ?_
  · have h : ofHom (algebraMap (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] R)) ≫
        ofHom (geometricFrobeniusTensor k R).toRingHom =
        ofHom (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k
          (AlgebraicClosure k)).toRingEquiv.toRingHom ≫
          ofHom (algebraMap (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] R)) := by
      ext x
      simp [geometricFrobeniusTensor]
    rw [Category.assoc, Category.assoc, ← Spec.map_comp, h, Spec.map_comp,
      geometricFiberIsoSpec_hom_algebraMap_assoc, geometricFiberIsoSpec_hom_algebraMap,
      geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure,
      specGeometricFrobenius_hom]
  · have h : ofHom (Algebra.TensorProduct.includeRight :
          R →ₐ[k] AlgebraicClosure k ⊗[k] R).toRingHom ≫
        ofHom (geometricFrobeniusTensor k R).toRingHom =
        ofHom (Algebra.TensorProduct.includeRight :
          R →ₐ[k] AlgebraicClosure k ⊗[k] R).toRingHom := by
      ext x
      exact congrArg (· ⊗ₜ[k] x) (map_one (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k _))
    rw [Category.assoc, Category.assoc, ← Spec.map_comp, h, geometricFiberIsoSpec_hom_includeRight,
      geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc]

/-- Under `X₀ ×_k k̄ ≅ Spec (k̄ ⊗[k] R)`, the `m`-th power of the geometric Galois Frobenius acts
on global sections as `(σ ⊗ 𝟙) ^ m`. -/
theorem geometricGaloisFrobenius_pow_hom_comp_geometricFiberIsoSpec_hom [Fintype k] (m : ℕ) :
    (f.geometricGaloisFrobenius ^ m).asIso.hom ≫ (geometricFiberIsoSpec f eR heR).hom =
      (geometricFiberIsoSpec f eR heR).hom ≫
        Spec.map (ofHom (geometricFrobeniusTensor k R ^ m).toRingHom) := by
  induction m with
  | zero =>
    have h : ofHom (1 : AlgebraicClosure k ⊗[k] R ≃ₐ[k] AlgebraicClosure k ⊗[k] R).toRingHom =
      𝟙 (of (AlgebraicClosure k ⊗[k] R)) := rfl
    rw [pow_zero, pow_zero, h, Spec.map_id, Category.comp_id]
    exact Category.id_comp _
  | succ m ih =>
    rw [pow_succ, Aut.mul_asIso, Iso.trans_hom, Category.assoc, ih,
      reassoc_of% geometricGaloisFrobenius_hom_comp_geometricFiberIsoSpec_hom, ← Spec.map_comp,
      pow_succ']
    rfl

end Scheme.Hom

end AlgebraicGeometry
