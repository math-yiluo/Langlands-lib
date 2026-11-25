/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Unramified.Locus
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.Unramified.Field

/-!
# A finite generically étale map from an affine curve to the affine line

Let `C` be a smooth affine curve over a finite field `k`. We construct a finite morphism
`g : C ⟶ 𝔸¹_k` over `k` which is étale over a dense open of `𝔸¹_k`
(blueprint `lemma-finite-generically-etale-map-line--1`).

Instead of the smooth projective completion and Riemann–Roch used in the blueprint, we use a
separable variant of Noether normalization for the coordinate ring `A = Γ(C, ⊤)`:

* Noether normalization gives `x : A` with `A` finite over `k[x]`;
* smoothness gives `a : A` such that `d a` spans the one-dimensional `Ω[K⁄k]`, where `K` is the
  function field;
* Nagata's trick: `A` is finite over `k[s]` for `s = x ^ (p ^ N) - a` with `N` large, and
  `d s = - d a` since `p = 0` in `k`;
* hence `Ω[K⁄k[s]] = 0`, so `k[s] → A` is unramified at the generic point, hence over a
  nonempty principal open of `k[s]` (the unramified locus is open and finite maps are closed),
  and `A` is flat over the principal ideal domain `k[s]`.

## Main statements

- `Algebra.exists_finite_formallyUnramified_away`: the algebraic statement.
- `AlgebraicGeometry.finrank_kaehlerDifferential_functionField`: the function field of a scheme
  smooth of relative dimension `n` over a field `k` has `n`-dimensional `Ω[K⁄k]`.
- `AlgebraicGeometry.AffineSpace.exists_isFinite_etale_morphismRestrict`: for a smooth affine
  integral curve over a perfect field of positive characteristic.
- `AlgebraicGeometry.AffineSpace.exists_isFinite_etale_morphismRestrict_of_finite`: for a smooth
  affine geometrically connected curve over a finite field.
- `AlgebraicGeometry.AffineSpace.exists_isOpenImmersion_isFinite_etale_morphismRestrict`: the
  statement in the shape of blueprint `lemma-finite-generically-etale-map-line--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial KaehlerDifferential

/-- **Separable Noether normalization for curves in positive characteristic.**
Let `A` be a finitely generated domain of dimension at most one over a perfect field `k` of
characteristic `p > 0`, with fraction field `K` such that `Ω[K⁄k]` is one-dimensional. Then there
is an injective `k`-algebra map `ψ : k[X] → A` making `A` a finite flat `k[X]`-algebra which is
unramified away from some nonzero `h : k[X]`.

Algebraic core of blueprint `lemma-finite-generically-etale-map-line--1`. -/
theorem Algebra.exists_finite_formallyUnramified_away {k A K : Type*} [Field k] [PerfectField k]
    (p : ℕ) [hp : Fact p.Prime] [CharP k p] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : ringKrullDim A ≤ 1) [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]
    (hΩ : Module.finrank K Ω[K⁄k] = 1) :
    ∃ ψ : k[X] →ₐ[k] A, ψ.Finite ∧ Function.Injective ψ ∧ ψ.toRingHom.Flat ∧
      ∃ h : k[X], h ≠ 0 ∧ (Localization.awayMap ψ.toRingHom h).FormallyUnramified := by
  obtain ⟨a, ha⟩ := exists_span_D_algebraMap_eq_top (R := k) (nonZeroDivisors A) hΩ
  obtain ⟨g, hg⟩ := Algebra.exists_finite_algHom_polynomial_of_ringKrullDim_le_one k A hA
  have hgx : g = aeval (g X) := algHom_ext (by simp)
  obtain ⟨m, hm⟩ := exists_finite_aeval_pow_sub (hgx ▸ hg) a
  set s := g X ^ p ^ (m + 1) - a
  have hψ : (aeval (R := k) s).Finite :=
    hm _ ((Nat.lt_succ_self m).trans (Nat.lt_pow_self hp.out.one_lt))
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hDs : Submodule.span K {D k K (algebraMap A K s)} = ⊤ := by
    have : D k K (algebraMap A K s) = (-1 : K) • D k K (algebraMap A K a) := by
      rw [map_sub, map_sub, map_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K,
        Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega), zero_smul, zero_sub, neg_one_smul]
    rw [this, Submodule.span_singleton_smul_eq isUnit_one.neg, ha]
  set ψ : k[X] →ₐ[k] A := aeval s with hψdef
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hf0
    have halg : IsAlgebraic k (algebraMap A K s) :=
      ⟨f, hf0, by rw [aeval_algebraMap_apply, ← hψdef, hf, map_zero]⟩
    rw [D_eq_zero_of_isAlgebraic halg, Submodule.span_zero_singleton] at hDs
    rw [← finrank_top, ← hDs, finrank_bot] at hΩ
    exact zero_ne_one hΩ
  let : Algebra k[X] A := ψ.toRingHom.toAlgebra
  let : Algebra k[X] K := ((algebraMap A K).comp ψ.toRingHom).toAlgebra
  have : IsScalarTower k[X] A K := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k[X] A := .of_algebraMap_eq fun c ↦ (ψ.commutes c).symm
  have : IsScalarTower k k[X] K := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k A K, IsScalarTower.algebraMap_apply k k[X] A,
      ← IsScalarTower.algebraMap_apply k[X] A K]
  have : Module.Finite k[X] A := hψ
  have hK : Algebra.FormallyUnramified k[X] K := by
    rw [Algebra.formallyUnramified_iff]
    have hmap : (KaehlerDifferential.map k k[X] K K) (D k K (algebraMap A K s)) = 0 := by
      have : algebraMap A K s = algebraMap k[X] K X := by
        rw [IsScalarTower.algebraMap_apply k[X] A K]
        simp [RingHom.algebraMap_toAlgebra, ψ]
      rw [this, map_D, Algebra.algebraMap_self, RingHom.id_apply, Derivation.map_algebraMap]
    refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective k k[X] K ω
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hDs ▸ Submodule.mem_top (x := ω))
    rw [map_smul, hmap, smul_zero]
  have : IsLocalization (⊥ : Ideal A).primeCompl K := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus k[X] A :=
    Algebra.FormallyUnramified.of_equiv ((IsLocalization.algEquiv (⊥ : Ideal A).primeCompl K
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k[X])
  have hZ : IsClosed (PrimeSpectrum.comap (algebraMap k[X] A) ''
      (Algebra.unramifiedLocus k[X] A)ᶜ) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x ↦ Algebra.IsIntegral.isIntegral x) _
      Algebra.isOpen_unramifiedLocus.isClosed_compl
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
  have hIbot : ¬ (I : Set k[X]) ⊆ (⊥ : Ideal k[X]) := by
    intro hle
    obtain ⟨P, hP, hPe⟩ : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k[X]) ∈
        PrimeSpectrum.comap (algebraMap k[X] A) '' (Algebra.unramifiedLocus k[X] A)ᶜ := by
      rw [hI]
      exact hle
    have : P.asIdeal = ⊥ := Ideal.eq_bot_of_under_eq_bot (congrArg PrimeSpectrum.asIdeal hPe)
    obtain rfl : P = ⟨⊥, Ideal.isPrime_bot⟩ := PrimeSpectrum.ext this
    exact hP hbot
  obtain ⟨h, hhI, hh0⟩ := Set.not_subset.mp hIbot
  have : Module.IsTorsionFree k[X] A := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  refine ⟨ψ, hψ, hinj, inferInstanceAs (Module.Flat k[X] A), h, hh0, ?_⟩
  have hU : Algebra.FormallyUnramified k[X] (Localization.Away (ψ h)) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff]
    intro P hP
    by_contra hPZ
    have : PrimeSpectrum.comap (algebraMap k[X] A) P ∈ PrimeSpectrum.zeroLocus (I : Set k[X]) :=
      hI ▸ ⟨P, hPZ, rfl⟩
    exact hP (this hhI)
  let := (Localization.awayMap ψ.toRingHom h).toAlgebra
  have : IsScalarTower k[X] (Localization.Away h) (Localization.Away (ψ h)) :=
    .of_algebraMap_eq fun f ↦ by
      simp [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq, IsScalarTower.algebraMap_apply k[X] A (Localization.Away (ψ h))]
  exact Algebra.FormallyUnramified.of_restrictScalars k[X] (Localization.Away h)
    (Localization.Away (ψ h))

namespace AlgebraicGeometry

/-- If `X` is an integral scheme smooth of relative dimension `n` over a field `k`, then the
Kähler differentials of its function field `K` over `k` form an `n`-dimensional `K`-vector space:
near the generic point, `X` is étale over `𝔸ⁿ_k`. The base ring is any ring `R` identified with
`Γ(Spec k, ⊤)` by `e`, e.g. `k` itself or `Γ(Spec k, ⊤)`. -/
theorem finrank_kaehlerDifferential_functionField {k R : Type u} [Field k] [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [Algebra R X.functionField] (e : R ≃+* Γ(Spec (.of k), ⊤))
    (hk : algebraMap R X.functionField = (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
      (f.appTop.hom.comp e.toRingHom)) :
    Module.finrank X.functionField Ω[X.functionField⁄R] = n := by
  have : Nontrivial R := e.toEquiv.nontrivial
  obtain ⟨U, -, V, hV, hx, e', H⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f)
      (genericPoint X)
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (f (genericPoint X)) z ▸ e' hx
  obtain ⟨φ, hφC, hφ⟩ := H.exists_etale_mvPolynomial
  have : Nonempty V := ⟨⟨genericPoint X, hx⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  let ε : MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) Γ(Spec (.of k), ⊤) :=
    MvPolynomial.mapEquiv _ e
  let : Algebra R Γ(X, V) := ((f.appLE ⊤ V e').hom.comp e.toRingHom).toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) Γ(X, V) := (φ.comp ε.toRingHom).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) Γ(X, V) := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra, ε, ← hφC]
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, V) :=
    RingHom.Etale.respectsIso.2 _ _ hφ
  have : IsScalarTower R Γ(X, V) X.functionField := .of_algebraMap_eq fun c ↦ by
    rw [hk]
    simp [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE]
  have e₁ := tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) Γ(X, V)
  have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄R] := .of_equiv e₁
  have hB : Module.finrank Γ(X, V) Ω[Γ(X, V)⁄R] = n := by
    rw [← e₁.finrank_eq, Module.finrank_baseChange, Module.finrank_eq_card_basis
      (mvPolynomialBasis R (Fin n)), Fintype.card_fin]
  rw [Module.finrank_of_isLocalizedModule_of_free X.functionField (nonZeroDivisors Γ(X, V))
    (KaehlerDifferential.map R R Γ(X, V) X.functionField), hB]


variable {k : Type u} [Field k]

namespace AffineSpace

/-- A smooth affine integral curve `C` over a perfect field `k` of positive characteristic admits
a finite morphism `g : C ⟶ 𝔸¹_k` over `k` which is étale over a dense open `V` of `𝔸¹_k`
(blueprint `lemma-finite-generically-etale-map-line--1`). -/
theorem exists_isFinite_etale_morphismRestrict [PerfectField k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (C : Scheme.{u}) [C.Over (Spec (.of k))] [IsAffine C] [IsIntegral C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] :
    ∃ g : C ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k)), g.IsOver (Spec (.of k)) ∧ IsFinite g ∧
      ∃ V : 𝔸(PUnit.{u + 1}; Spec (.of k)).Opens,
        Dense (V : Set 𝔸(PUnit.{u + 1}; Spec (.of k))) ∧ Etale (g ∣_ V) := by
  let s := C ↘ Spec (.of k)
  have : Smooth s := SmoothOfRelativeDimension.smooth 1 s
  let : Algebra k Γ(C, ⊤) := (s.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(C, ⊤) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType s inferInstance)
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  let : Algebra k C.functionField :=
    ((algebraMap Γ(C, ⊤) C.functionField).comp (algebraMap k Γ(C, ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, ⊤) C.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have := functionField_isFractionRing_of_isAffineOpen C ⊤ (isAffineOpen_top C)
  obtain ⟨ψ, hψ, -, hflat, h, hh0, hU⟩ := Algebra.exists_finite_formallyUnramified_away p
    (ringKrullDim_le_of_smoothOfRelativeDimension s 1)
    (finrank_kaehlerDifferential_functionField s 1
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm rfl)
  let e := MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}
  let φ : MvPolynomial PUnit.{u + 1} k →ₐ[k] Γ(C, ⊤) := ψ.comp e.toAlgHom
  have hφ : φ.Finite := RingHom.Finite.comp hψ (RingHom.Finite.of_surjective _ e.surjective)
  let F := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let ε : Spec (.of k[X]) ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k)) :=
    Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ (SpecIso PUnit.{u + 1} (.of k)).inv
  have hg : C.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (SpecIso PUnit.{u + 1} (.of k)).inv = C.isoSpec.hom ≫ F ≫ ε := by
    simp only [F, ε, ← Spec.map_comp_assoc]
    rfl
  refine ⟨C.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (SpecIso PUnit.{u + 1} (.of k)).inv, ⟨?_⟩, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have e : φ.toRingHom.comp MvPolynomial.C =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom := by
      ext a
      exact φ.commutes a
    rw [e, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  · have : IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr hφ
    infer_instance
  rw [hg]
  let W : (Spec (.of k[X])).Opens := PrimeSpectrum.basicOpen h
  have : Flat F := HasRingHomProperty.Spec_iff.mpr hflat
  have : IsFinite F := (IsFinite.SpecMap_iff _).mpr hψ
  have : FormallyUnramified (F ∣_ W) := (MorphismProperty.arrow_mk_iso_iff @FormallyUnramified
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom ψ.toRingHom) h)).mpr
    (HasRingHomProperty.Spec_iff.mpr hU)
  have : Etale (F ∣_ W) := Etale.of_formallyUnramified_of_flat _
  have : IsIso ε := by
    dsimp [ε]
    infer_instance
  refine ⟨ε ''ᵁ W, ?_, ?_⟩
  · have hW : Dense (W : Set (Spec (.of k[X]))) :=
      W.isOpen.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, (PrimeSpectrum.mem_basicOpen _ _).mpr hh0⟩
    simpa using ε.homeomorph.surjective.denseRange.dense_image ε.homeomorph.continuous hW
  · have : Etale ((C.isoSpec.hom ≫ F ≫ ε) ∣_ (ε ''ᵁ W) ≫ (ε ''ᵁ W).ι) := by
      rw [morphismRestrict_ι]
      have hpre : (C.isoSpec.hom ≫ F ≫ ε) ⁻¹ᵁ (ε ''ᵁ W) = C.isoSpec.hom ⁻¹ᵁ (F ⁻¹ᵁ W) := by
        simp [Scheme.Hom.preimage_image_eq]
      rw [hpre, ← Category.assoc, ← morphismRestrict_ι, Category.assoc, ← Category.assoc _ F,
        ← morphismRestrict_ι]
      infer_instance
    exact Etale.of_comp _ (ε ''ᵁ W).ι


/-- **Finite map to the affine line** (blueprint `lemma-finite-generically-etale-map-line--1`, with
`C' = C`). A smooth affine geometrically connected curve `C` over a finite field `k` admits a finite
morphism `g : C ⟶ 𝔸¹_k` over `k` which is étale over a dense open `V` of `𝔸¹_k`. -/
theorem exists_isFinite_etale_morphismRestrict_of_finite [Finite k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] :
    ∃ g : C ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k)), g.IsOver (Spec (.of k)) ∧ IsFinite g ∧
      ∃ V : 𝔸(PUnit.{u + 1}; Spec (.of k)).Opens,
        Dense (V : Set 𝔸(PUnit.{u + 1}; Spec (.of k))) ∧ Etale (g ∣_ V) := by
  have : Smooth (C ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular C := IsRegular.of_smooth (C ↘ Spec (.of k))
  have : ConnectedSpace C :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  have : IsIntegral C := IsRegular.isIntegral C
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  exact exists_isFinite_etale_morphismRestrict (ringChar k) C

/-- **Finite map to the affine line**, in the shape of blueprint
`lemma-finite-generically-etale-map-line--1`. Let `C` be a smooth affine geometrically connected
curve over a finite field `k`. There is a smooth geometrically connected curve `C'` over `k`
containing `C` as a dense open with finite complement, and a finite morphism `g : C' ⟶ 𝔸¹_k` over
`k` which is étale over a dense open of `𝔸¹_k`. One can take `C' = C`, see
`exists_isFinite_etale_morphismRestrict_of_finite`. -/
theorem exists_isOpenImmersion_isFinite_etale_morphismRestrict [Finite k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] :
    ∃ (C' : Scheme.{u}) (π : C' ⟶ Spec (.of k)) (ι : C ⟶ C'), IsOpenImmersion ι ∧
      ι ≫ π = C ↘ Spec (.of k) ∧ Dense (Set.range ι) ∧ (Set.range ι)ᶜ.Finite ∧
      SmoothOfRelativeDimension 1 π ∧ GeometricallyConnected π ∧
      ∃ g : C' ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        g ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k) = π ∧ IsFinite g ∧
        ∃ V : 𝔸(PUnit.{u + 1}; Spec (.of k)).Opens,
          Dense (V : Set 𝔸(PUnit.{u + 1}; Spec (.of k))) ∧ Etale (g ∣_ V) := by
  obtain ⟨g, hg, hgf, V, hV, hgV⟩ := exists_isFinite_etale_morphismRestrict_of_finite (k := k) C
  refine ⟨C, C ↘ Spec (.of k), 𝟙 C, inferInstance, Category.id_comp _, ?_, ?_, inferInstance,
    inferInstance, g, comp_over g (Spec (.of k)), hgf, V, hV, hgV⟩
  · simp [dense_univ]
  · simp

end AffineSpace

end AlgebraicGeometry
