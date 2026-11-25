/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Infinity
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension

/-!
# Higher direct images of the affine line at a geometric generic point

Let `K` be a field, `B = Spec K[y₁, …, y_c]` and `f : 𝔸¹_B ⟶ B` the projection. At a geometric
point `s` of `B` lying over the generic point (equivalently, whose residue field has
transcendence degree at least `c` over `K`), the stalk of `Rᵠf_* M` vanishes for `q ≥ 2` and
every torsion sheaf `M`
(`AlgebraicGeometry.AffineSpace.isZero_upperStar_rightDerived_lowerStar_of_generic`).

Indeed the strict henselization of `B` at `s` is a separably closed field `L`
(`AlgebraicGeometry.Scheme.isField_strictHenselization`), so by the stalk formula it suffices
that `Hᵠ(𝔸¹_L, M|) = 0`, which holds since `𝔸¹_L` is an affine curve over a separably closed
field (`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

open Scheme Etale

/-- **The geometric generic stalk.** Let `K` be a field, `B = Spec K[y₁, …, y_c]` and
`f : 𝔸¹_B ⟶ B` the projection. If `s` is a geometric point of `B` whose residue field has
transcendence degree at least `c` over `K` (so that `s` lies over the generic point), then for
every torsion abelian étale sheaf `M` on `𝔸¹_B` and `q ≥ 2` the stalk of `Rᵠf_* M` at `s`
vanishes. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_generic {K : Type u} [Field K] {c : ℕ}
    (M : Sheaf 𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (hM : M.IsTorsion) (q : ℕ) (hq : 2 ≤ q)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin c) K)))
    (hs : (c : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω))) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))) ↘
        Spec (.of (MvPolynomial (Fin c) K)))_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj M)) := by
  classical
  let A := MvPolynomial (Fin c) K
  let B : Scheme.{u} := Spec (.of A)
  set y := s (IsLocalRing.closedPoint Ω)
  -- `s` lies over the generic point of `B`
  have hp : y.asIdeal = ⊥ := by
    by_contra hne
    rw [residueFieldTrdeg_Spec] at hs
    have : FaithfulSMul K (A ⧸ y.asIdeal) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K (A ⧸ y.asIdeal)).injective
    have : FaithfulSMul (A ⧸ y.asIdeal) y.asIdeal.ResidueField :=
      (faithfulSMul_iff_algebraMap_injective _ _).2
        y.asIdeal.injective_algebraMap_quotient_residueField
    have : Algebra.IsAlgebraic (A ⧸ y.asIdeal) y.asIdeal.ResidueField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ y.asIdeal))
    have htr : Algebra.trdeg K (A ⧸ y.asIdeal) = Algebra.trdeg K y.asIdeal.ResidueField := by
      rw [← trdeg_add_eq K (A ⧸ y.asIdeal) (A := y.asIdeal.ResidueField),
        trdeg_eq_zero (R := A ⧸ y.asIdeal) (A := y.asIdeal.ResidueField), add_zero]
    obtain ⟨m, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K (A ⧸ y.asIdeal)
    have hdim := ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hinj hfin
    have htrm := Algebra.trdeg_eq_of_ringKrullDim_eq K (A ⧸ y.asIdeal) hdim
    have hlt := ringKrullDim_quotient_lt_of_finiteType K A y.asIdeal hne
    rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] at hlt
    rw [← htr, htrm] at hs
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at hlt
    norm_cast at hs hlt
    omega
  have hinj : Function.Injective (Spec.preimage s).hom := by
    obtain ⟨g, hg⟩ := exists_spec_preimage_eq_comp s
    rw [hg, CommRingCat.hom_comp]
    refine g.hom.injective.comp ?_
    rw [CommRingCat.hom_ofHom, RingHom.injective_iff_ker_eq_bot,
      Ideal.ker_algebraMap_residueField]
    exact hp
  let R := strictHenselization s
  let t := strictLocalizationToBase s
  have hfield : IsField R := isField_strictHenselization s hinj
  let L := IsLocalRing.ResidueField R
  have hres : Function.Injective (IsLocalRing.residue R) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hfield
  let ρ : R ≃+* L := RingEquiv.ofBijective _ ⟨hres, IsLocalRing.residue_surjective⟩
  let ψ : Spec (.of L) ≅ Spec R := Scheme.Spec.mapIso ρ.toCommRingCatIso.op
  have : IsCurve (𝔸(PUnit.{u + 1}; Spec (.of L)) ↘ Spec (.of L)) := by
    refine { krullDim_le_one := ?_ }
    refine (IsHomeomorph.topologicalKrullDim_eq _
        (AffineSpace.SpecIso PUnit.{u + 1} (.of L)).hom.homeomorph.isHomeomorph).trans_le ?_
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans_le ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  have hcurve := (IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed
    (𝔸(PUnit.{u + 1}; Spec (.of L)) ↘ Spec (.of L))).2 inferInstance
  let h := 𝔸(PUnit.{u + 1}; B) ↘ B
  let φ : 𝔸(PUnit.{u + 1}; Spec (.of L)) ⟶ pullback h t :=
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (ψ.hom ≫ t)).isoPullback.hom ≫
      pullback.map h (ψ.hom ≫ t) h t (𝟙 _) ψ.hom (𝟙 _) (by simp) (by simp)
  have hY := hcurve.of_isUniversalHomeomorphism φ
  have key := isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H h (𝟙 B) M s q
    (by omega) (by
      exact hY _ (Etale.isTorsion_upperStar _ hM) q (by omega))
  simpa using key

end AlgebraicGeometry.AffineSpace
