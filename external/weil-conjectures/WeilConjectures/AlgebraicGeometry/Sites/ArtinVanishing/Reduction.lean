/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.AffineSpace
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Reductions in the affine Artin vanishing theorem

We complete the induction proving the affine Artin bound `ArtinBound d` in every dimension `d`
(`AlgebraicGeometry.Scheme.artinBound`):

* over an algebraically closed field, Noether normalization gives a finite morphism from an
  affine scheme of finite type and dimension `≤ d` to `𝔸ᵉ`, `e ≤ d`, and finite direct images
  preserve cohomology, which reduces to affine space
  (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_mvPolynomial`);
* over an arbitrary field one passes to an algebraic closure
  (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme



/-- `cd_tor(𝔸ᵉ_K) ≤ e` over an algebraically closed field `K`, assuming the affine Artin bound
in dimensions `< e`. -/
theorem hasTorsionCohomologicalDimensionLE_mvPolynomial {K : Type u} [Field K] [IsAlgClosed K]
    (e : ℕ) (IH : ∀ e' < e, ArtinBound.{u} e') :
    (Spec (.of (MvPolynomial (Fin e) K))).HasTorsionCohomologicalDimensionLE e := by
  cases e with
  | zero =>
    let φ : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Fin 0) K)) :=
      Spec.map (CommRingCat.ofHom (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingHom)
    have : IsIso φ := by
      have : IsIso (CommRingCat.ofHom (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingHom) :=
        (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv.toCommRingCatIso.isIso_hom
      infer_instance
    exact (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K).of_isUniversalHomeomorphism φ
  | succ c =>
    let ε : MvPolynomial (Fin (c + 1)) K ≃+* MvPolynomial PUnit.{u + 1} (MvPolynomial (Fin c) K) :=
      (MvPolynomial.finSuccEquiv K c).toRingEquiv.trans
        (MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin c) K) PUnit.{u + 1}).symm.toRingEquiv
    let φ : 𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))) ⟶
        Spec (.of (MvPolynomial (Fin (c + 1)) K)) :=
      (AffineSpace.SpecIso PUnit.{u + 1} (.of (MvPolynomial (Fin c) K))).hom ≫
        Spec.map (CommRingCat.ofHom ε.toRingHom)
    have : IsIso φ := by
      have : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
      infer_instance
    exact HasTorsionCohomologicalDimensionLE.of_isUniversalHomeomorphism φ
      (hasTorsionCohomologicalDimensionLE_affineLine_mvPolynomial IH)

/-- A finite morphism `π : X ⟶ Y` with `X` quasi-compact and quasi-separated transfers a torsion
cohomological dimension bound from `Y` to `X`: finite direct images preserve cohomology
(`AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite`). -/
theorem HasTorsionCohomologicalDimensionLE.of_isFinite {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (π : X ⟶ Y) [IsFinite π] {d : ℕ}
    (h : Y.HasTorsionCohomologicalDimensionLE d) : X.HasTorsionCohomologicalDimensionLE d :=
  hasTorsionCohomologicalDimensionLE_of_nsmul fun M _ hn hM m hm ↦
    have := h _ (isTorsion_of_nsmul_id_eq_zero hn
      (Functor.nsmul_id_obj_eq_zero (Etale.lowerStar AddCommGrpCat.{u + 1} π) hM)) m hm
    (Etale.bijective_edgeMap_of_isFinite π M m).2.subsingleton

/-- The affine Artin bound over an algebraically closed field: if `K` is algebraically closed
and the bound holds in dimensions `< d`, then `cd_tor(X) ≤ d` for every affine `K`-scheme `X` of
finite type and dimension at most `d`. By Noether normalization `X` is finite over `𝔸ᵉ_K` with
`e ≤ d`. -/
theorem hasTorsionCohomologicalDimensionLE_of_isAlgClosed {K : Type u} [Field K]
    [IsAlgClosed K] {d : ℕ} (IH : ∀ e < d, ArtinBound.{u} e) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE d := by
  let R := Γ(X, ⊤)
  let : Algebra K R := ((Scheme.ΓSpecIso (.of K)).inv ≫ a.appTop).hom.toAlgebra
  have : Algebra.FiniteType K R := by
    have ha : a.appTop.hom.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 inferInstance
    exact RingHom.FiniteType.comp ha (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have hdim : ringKrullDim R ≤ d := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    refine le_trans (le_of_eq ?_) hX
    have h := IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph
    exact h.symm
  obtain ⟨e, he, φ, hφ⟩ : ∃ e ≤ d, ∃ φ : MvPolynomial (Fin e) K →ₐ[K] R, φ.Finite := by
    cases subsingleton_or_nontrivial R with
    | inl hR =>
      refine ⟨0, Nat.zero_le _, MvPolynomial.aeval (fun _ ↦ 0), ?_⟩
      exact RingHom.Finite.of_surjective _ fun y ↦ ⟨0, Subsingleton.elim _ _⟩
    | inr hR =>
      obtain ⟨e, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K R
      refine ⟨e, ?_, φ, hfin⟩
      have := ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial φ hinj hfin
      rw [this] at hdim
      exact_mod_cast hdim
  let π : X ⟶ Spec (.of (MvPolynomial (Fin e) K)) :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
  have : IsFinite π := by
    have : IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
      rw [IsFinite.SpecMap_iff]
      exact hφ
    infer_instance
  exact HasTorsionCohomologicalDimensionLE.of_isFinite π
    ((hasTorsionCohomologicalDimensionLE_mvPolynomial e fun e' he' ↦ IH e' (by omega)).mono he)

/-- **The affine Artin bound in every dimension**: for every field `K` with `cd_tor(K) ≤ c` and
every affine `K`-scheme `X` of finite type and dimension at most `d`, `cd_tor(X) ≤ d + c`. -/
theorem artinBound (d : ℕ) : ArtinBound.{u} d := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro L _ c hL X a ha hXa hX
  let L' := AlgebraicClosure L
  let q := Spec.map (CommRingCat.ofHom (algebraMap L L'))
  have : QuasiCompact a := inferInstance
  have hX' : topologicalKrullDim (Limits.pullback a q : Scheme.{u}) ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_pullback_le_of_field a q).trans hX
  have := hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure L' a hL
    (hasTorsionCohomologicalDimensionLE_of_isAlgClosed IH (pullback.snd a q) hX')
  rwa [add_comm] at this

end AlgebraicGeometry.Scheme
