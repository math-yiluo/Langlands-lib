/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The coordinate hyperplane of affine space and the compactification of a coordinate

Let `k` be a field and `𝔸^{N+1}_k = Spec k[X₀, …, X_N]`
(`AlgebraicGeometry.polyAffine k (N + 1)`).
This file provides

* the coordinate hyperplane `V(X_N) ⊆ 𝔸^{N+1}_k` (`AlgebraicGeometry.polyAffineHyperplane`),
  whose inverse image under the projection `𝔸^{N+2}_k ⟶ 𝔸^{N+1}_k` forgetting `X₀` is again the
  coordinate hyperplane (`AlgebraicGeometry.comap_polyAffineProj_polyAffineHyperplane`);
* the compactification of the coordinate `X₀`: the open immersion
  `𝔸^{N+1}_k ⟶ ℙ¹_{𝔸^N_k}`, `x ↦ [X₀(x) : 1]`, over the projection forgetting `X₀`
  (`AlgebraicGeometry.polyAffineChart`), whose image is the complement of the section at infinity
  (`AlgebraicGeometry.range_polyAffineChart`).

These are the coordinates used in the proof of blueprint
`theorem-verdier-s-theorem-specialization-zero`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme ProjectiveLine

/-! ### The section at infinity over a base -/

section Infinity

variable {S : Scheme.{u}} (B : Over S)

/-- The section at infinity `∞ : B ⟶ ℙ¹_B`, as a morphism of schemes over `S`. -/
noncomputable def Scheme.overProjectiveLineInfinity : B ⟶ overProjectiveLine B :=
  Over.homMk (infinity B.left) (by simp [overProjectiveLine])

@[simp]
lemma Scheme.overProjectiveLineInfinity_left :
    (overProjectiveLineInfinity B).left = infinity B.left :=
  rfl

@[reassoc (attr := simp)]
lemma Scheme.overProjectiveLineInfinity_proj :
    overProjectiveLineInfinity B ≫ overProjectiveLineProj B = 𝟙 B := by
  ext1
  exact infinity_over

end Infinity

variable (k : Type u) [Field k]

/-! ### The coordinate hyperplane -/

/-- The coordinate `Xᵢ` of `𝔸ᴺ_k = Spec k[X₀, …, X_{N-1}]`, as a global function. -/
noncomputable def polyAffineCoord {N : ℕ} (i : Fin N) : Γ((polyAffine k N).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (MvPolynomial (Fin N) k))).inv (MvPolynomial.X i)

lemma polyAffineCoord_ne_zero {N : ℕ} (i : Fin N) : polyAffineCoord k i ≠ 0 := by
  intro h
  refine MvPolynomial.X_ne_zero (R := k) i ?_
  simpa [polyAffineCoord] using congrArg (Scheme.ΓSpecIso (.of (MvPolynomial (Fin N) k))).hom h

instance (N : ℕ) : IsAffine (polyAffine k N).left :=
  inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin N) k))))

instance (N : ℕ) : IsIntegral (polyAffine k N).left :=
  inferInstanceAs (IsIntegral (Spec (.of (MvPolynomial (Fin N) k))))

/-- The coordinate hyperplane `V(X_N) ⊆ 𝔸^{N+1}_k`. -/
noncomputable def polyAffineHyperplane (N : ℕ) : (polyAffine k (N + 1)).left.IdealSheafData :=
  IdealSheafData.ofIdealTop (Ideal.span {polyAffineCoord k (Fin.last N)})

/-- The inverse image of the coordinate hyperplane `V(X_N) ⊆ 𝔸^{N+1}_k` under the projection
`𝔸^{N+2}_k ⟶ 𝔸^{N+1}_k` forgetting `X₀` is the coordinate hyperplane `V(X_{N+1})`. -/
lemma comap_polyAffineProj_polyAffineHyperplane (N : ℕ) :
    (polyAffineHyperplane k N).comap (polyAffineProj k (N + 1)).left =
      polyAffineHyperplane k (N + 1) := by
  have h : (Spec.map (CommRingCat.ofHom (polyAffineProjRingHom k (N + 1)))).appTop
      (polyAffineCoord k (Fin.last N)) = polyAffineCoord k (Fin.last (N + 1)) := by
    rw [polyAffineCoord, polyAffineCoord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp [polyAffineProjRingHom]
  refine IdealSheafData.ext_of_isAffine ?_
  rw [IdealSheafData.ideal_top_comap_of_isAffine, polyAffineHyperplane, polyAffineHyperplane,
    IdealSheafData.ideal_top_ofIdealTop, IdealSheafData.ideal_top_ofIdealTop, Ideal.map_span,
    Set.image_singleton]
  exact congrArg (fun a ↦ Ideal.span {a}) h

/-- Affine space over a field is a normal scheme. -/
lemma isNormalScheme_polyAffine (N : ℕ) : IsNormalScheme (polyAffine k N).left := by
  refine ⟨inferInstance, fun x ↦ ⟨inferInstance, ?_⟩⟩
  let : Algebra (MvPolynomial (Fin N) k) ((polyAffine k N).left.presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (MvPolynomial (Fin N) k) x
  have : IsLocalization.AtPrime ((polyAffine k N).left.presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (MvPolynomial (Fin N) k) x
  exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
    x.asIdeal.primeCompl_le_nonZeroDivisors

/-- A point of `𝔸^{N+1}_k` lies on the coordinate hyperplane `V(X_N)` iff `X_N` lies in the
corresponding prime. -/
lemma mem_range_polyAffineHyperplane_subschemeι (N : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin (N + 1)) k)) :
    x ∈ Set.range (polyAffineHyperplane k N).subschemeι.base ↔
      MvPolynomial.X (Fin.last N) ∈ x.asIdeal := by
  have h : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin (N + 1)) k))).inv ⁻¹'
      {polyAffineCoord k (Fin.last N)} = {MvPolynomial.X (Fin.last N)} := by
    ext a
    exact (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).1.eq_iff
  have h' := Spec_zeroLocus (R := .of (MvPolynomial (Fin (N + 1)) k))
    {polyAffineCoord k (Fin.last N)}
  rw [h] at h'
  rw [polyAffineHyperplane, IdealSheafData.range_subschemeι_ofIdealTop_span]
  exact (Set.ext_iff.1 h' x).trans
    ((PrimeSpectrum.mem_zeroLocus _ _).trans Set.singleton_subset_iff)

/-- The ideal of polynomials with vanishing constant term is maximal. -/
private lemma isMaximal_ker_constantCoeff (σ : Type*) :
    (RingHom.ker (MvPolynomial.constantCoeff (σ := σ) (R := k))).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun r ↦
    ⟨MvPolynomial.C r, MvPolynomial.constantCoeff_C _ r⟩

/-- The coordinate hyperplane of the affine line is a single point. -/
lemma subsingleton_polyAffineHyperplane_subscheme :
    Subsingleton (polyAffineHyperplane k 0).subscheme := by
  have key (y : PrimeSpectrum (MvPolynomial (Fin 1) k))
      (hy : y ∈ Set.range (polyAffineHyperplane k 0).subschemeι.base) :
      RingHom.ker MvPolynomial.constantCoeff = y.asIdeal := by
    rw [mem_range_polyAffineHyperplane_subschemeι] at hy
    refine (isMaximal_ker_constantCoeff k _).eq_of_le
      y.isPrime.ne_top fun f hf ↦ ?_
    have hspan : f ∈ Ideal.span (MvPolynomial.X '' Set.univ) := by
      refine MvPolynomial.mem_ideal_span_X_image.2 fun m hm ↦ ?_
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 (show m ≠ 0 by
        rintro rfl
        exact MvPolynomial.mem_support_iff.1 hm hf)
      exact ⟨i, Set.mem_univ _, hi⟩
    refine Ideal.span_le.2 ?_ hspan
    rintro _ ⟨i, -, rfl⟩
    rwa [Subsingleton.elim i (Fin.last 0)]
  refine ⟨fun a b ↦ (polyAffineHyperplane k 0).subschemeι.isClosedEmbedding.injective ?_⟩
  exact PrimeSpectrum.ext ((key _ ⟨a, rfl⟩).symm.trans (key _ ⟨b, rfl⟩))

/-- The coordinate hyperplane is nonempty. -/
lemma nonempty_polyAffineHyperplane_subscheme (N : ℕ) :
    Nonempty (polyAffineHyperplane k N).subscheme := by
  let y : PrimeSpectrum (MvPolynomial (Fin (N + 1)) k) :=
    ⟨RingHom.ker MvPolynomial.constantCoeff,
      (isMaximal_ker_constantCoeff k _).isPrime⟩
  obtain ⟨a, -⟩ := (mem_range_polyAffineHyperplane_subschemeι k N y).2
    (RingHom.mem_ker.2 (MvPolynomial.constantCoeff_X _ _))
  exact ⟨a⟩

/-! ### The compactification of the coordinate `X₀` -/

/-- The open immersion `𝔸^{N+1}_k ⟶ ℙ¹_{𝔸^N_k}`, `x ↦ [X₀(x) : 1]`, over the projection
`𝔸^{N+1}_k ⟶ 𝔸^N_k` forgetting `X₀`. -/
noncomputable def polyAffineChart (N : ℕ) :
    polyAffine k (N + 1) ⟶ overProjectiveLine (polyAffine k N) :=
  Over.homMk (polyAffineSuccHom k N ≫ affineChart _) (by
    simp only [overProjectiveLine, polyAffine, Over.mk_left, Over.mk_hom, Category.assoc,
      affineChart_over_assoc, polyAffineSuccHom, AffineSpace.homOfVector_over_assoc]
    exact Over.w (polyAffineProj k N))

instance (N : ℕ) : IsOpenImmersion (polyAffineChart k N).left := by
  exact inferInstanceAs (IsOpenImmersion (polyAffineSuccHom k N ≫ affineChart _))

@[reassoc (attr := simp)]
lemma polyAffineChart_proj (N : ℕ) :
    polyAffineChart k N ≫ overProjectiveLineProj (polyAffine k N) = polyAffineProj k N := by
  ext1
  exact (Category.assoc _ _ _).trans
    ((polyAffineSuccHom k N ≫= affineChart_over _).trans (AffineSpace.homOfVector_over _ _))

/-- The image of `𝔸^{N+1}_k ⟶ ℙ¹_{𝔸^N_k}` is the complement of the section at infinity. -/
lemma range_polyAffineChart (N : ℕ) :
    Set.range (polyAffineChart k N).left.base =
      (Set.range (overProjectiveLineInfinity (polyAffine k N)).left.base)ᶜ := by
  have h : Set.range (polyAffineSuccHom k N ≫ affineChart _).base =
      (Set.range (infinity (Spec (.of (MvPolynomial (Fin N) k)))).base)ᶜ := by
    rw [range_infinity, compl_compl, ← Scheme.Hom.coe_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso]
  exact h

variable {k} in
/-- **A principal divisor of an affine scheme is the inverse image of a coordinate hyperplane**:
for an affine `k`-scheme `V` of finite type and a global function `h`, there is a closed immersion
`a : V ⟶ 𝔸^{n+1}_k` with `a⁻¹ V(X_n) = V(h)` schematically. -/
theorem exists_isClosedImmersion_comap_polyAffineHyperplane {V : Over (Spec (.of k))}
    [IsAffine V.left] [LocallyOfFiniteType V.hom] (h : Γ(V.left, ⊤)) :
    ∃ (n : ℕ) (a : V ⟶ polyAffine k (n + 1)), IsClosedImmersion a.left ∧
      (polyAffineHyperplane k n).comap a.left =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {h}) := by
  let φ : k →+* Γ(V.left, ⊤) := V.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hft : V.hom.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType V.hom ‹_›
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  let := φ.toAlgebra
  have : Algebra.FiniteType k Γ(V.left, ⊤) := hφ
  obtain ⟨N, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  let ψ' : MvPolynomial (Fin (N + 1)) k →ₐ[k] Γ(V.left, ⊤) :=
    MvPolynomial.aeval (Fin.lastCases h fun i ↦ ψ (MvPolynomial.X i))
  have hψ' : Function.Surjective ψ' := by
    have hcomp : ψ'.comp (MvPolynomial.rename Fin.castSucc) = ψ := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp [ψ']
    intro y
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨MvPolynomial.rename Fin.castSucc x, by rw [← AlgHom.comp_apply, hcomp]⟩
  refine ⟨N, Over.homMk (V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ'.toRingHom)) ?_,
    ?_, ?_⟩
  · dsimp only [polyAffine, Over.mk_hom]
    have hcomm : ψ'.toRingHom.comp (algebraMap k (MvPolynomial (Fin (N + 1)) k)) = φ := by
      ext r
      exact ψ'.commutes r
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomm,
      CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp,
      ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ'.toRingHom)) :=
      .spec_of_surjective _ hψ'
    exact inferInstanceAs (IsClosedImmersion
      (V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ'.toRingHom)))
  · have happ : (V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ'.toRingHom)).appTop
        (polyAffineCoord k (Fin.last N)) = h := by
      rw [Scheme.Hom.comp_appTop, polyAffineCoord, ← CommRingCat.comp_apply, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      simp [ψ']
    refine IdealSheafData.ext_of_isAffine ?_
    rw [IdealSheafData.ideal_top_comap_of_isAffine, polyAffineHyperplane,
      IdealSheafData.ideal_top_ofIdealTop, IdealSheafData.ideal_top_ofIdealTop, Ideal.map_span,
      Set.image_singleton]
    exact congrArg (fun a ↦ Ideal.span {a}) happ

end AlgebraicGeometry
