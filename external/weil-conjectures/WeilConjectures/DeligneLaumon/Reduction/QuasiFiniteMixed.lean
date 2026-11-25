/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.GeometricCoinvariants
import WeilConjectures.WeilSheaf.VerdierDualLocalization
import WeilConjectures.WeilSheaf.ConstantTwistWeight
import WeilConjectures.DeligneLaumon.Reduction.CompactSupport
import WeilConjectures.WeilSheaf.CohomologyExact

/-!
# Weil sheaves on a quasi-finite `k₀`-scheme are mixed

Let `X` be a separated `k₀`-scheme quasi-finite over `k₀`. Every Weil sheaf `F` on `X` is
`ι`-mixed (`AlgebraicGeometry.WeilSheaf.isMixed_of_locallyQuasiFinite`). This is the
dimension-zero case of the blueprint theorem `theorem-real-constructible-sheaves-are-mixed--1`.

## Implementation notes

We argue by strong induction on the total dimension `∑ₓ dim F_x̄` of the stalks at the finitely
many closed points. A nonzero `F` has a nonzero stalk, hence (by the formula for the local
polynomial of `H_c^0`) nonzero `H_c^0 = H^0`, hence nonzero global sections `Γ(X̄, F)`. A Frobenius
eigenvector `a` with eigenvalue `β` of `Γ(X̄, F)` gives a nonzero morphism `ℚ̄_ℓ(β) ⟶ F`, whose
image `I` is punctually pure, being a quotient of the constant twist `ℚ̄_ℓ(β)`. The cokernel of
`I ⟶ F` has smaller total stalk dimension, so it is mixed by induction, and so is `F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant Weil sheaf `ℚ̄_ℓ` is punctually `ι`-pure of weight `0`: its local Frobenius is
the identity (blueprint: `corollary-purity-cohomology-smooth-proper-variety`). -/
theorem isPunctuallyPureOfWeight_adicConstant :
    (adicConstant k₀ l X).IsPunctuallyPureOfWeight ι 0 := by
  intro x α hα
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
  have h : ((adicConstant k₀ l X).stalk x).frobenius = LinearEquiv.refl _ _ := by
    rw [stalk_eq_stalkAt]
    exact adicConstant_stalkAt_frobenius _ _ _
  rw [FrobeniusModule.frobeniusEnd_apply, h, LinearEquiv.refl_apply] at hv
  have h1 : (α - 1) • v = 0 := by
    rw [sub_smul, ← hv.1, one_smul, sub_self]
  obtain h1 | h1 := smul_eq_zero.1 h1
  · rw [sub_eq_zero.1 h1]
    simp
  · exact absurd h1 hv.2

/-- A Weil sheaf punctually `ι`-pure of weight `w` is mixed of weights at most `w`, by the
filtration `0 ⊆ F`. -/
theorem IsPunctuallyPureOfWeight.isMixedOfWeightsAtMost
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} {w : ℝ}
    (h : F.IsPunctuallyPureOfWeight ι w) : F.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure]
  exact ObjectProperty.le_filtrationClosure _ ⟨w, le_rfl, h⟩

/-- For a monomorphism `i : G ⟶ F` of Weil sheaves, the dimension of a stalk of `F` is the sum of
those of `G` and of the cokernel of `i`: the stalk functors are exact. -/
theorem finrank_stalk_cokernel_add_finrank_stalk
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F G : WeilSheaf k₀ l X} (i : G ⟶ F)
    [Mono i] (x : X.finitePoints) :
    Module.finrank (PadicAlgCl l) ((cokernel i).stalk x).carrier +
      Module.finrank (PadicAlgCl l) (G.stalk x).carrier =
      Module.finrank (PadicAlgCl l) (F.stalk x).carrier := by
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  have hex : LinearMap.range (stalkAtMap _ _ hs i) =
      LinearMap.ker (stalkAtMap _ _ hs (cokernel.π i)) :=
    range_stalkAtMap_eq_ker (ShortComplex.exact_cokernel i) _ _ hs
  have h := LinearMap.finrank_range_add_finrank_ker (stalkAtMap _ _ hs (cokernel.π i))
  rw [LinearMap.range_eq_top.2 (surjective_stalkAtMap _ _ hs _), finrank_top] at h
  simp only [stalk_eq_stalkAt]
  rw [← h, ← hex, LinearMap.finrank_range_of_inj (injective_stalkAtMap _ _ hs i)]

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyQuasiFinite (X ↘ Spec (CommRingCat.of k₀))]

/-- On a `k₀`-scheme quasi-finite over `k₀`, a Weil sheaf with a nonzero stalk has nonzero
compactly supported cohomology `H_c^0`: a `deg x`-th root `β` of a local Frobenius eigenvalue
at `x` has `β⁻¹` as a root of `det (1 - T F ∣ H_c^0)`. -/
theorem nontrivial_compactlySupportedCohomology_zero_of_not_isZero {F : WeilSheaf k₀ l X}
    (hF : ¬ IsZero F) : Nontrivial (F.compactlySupportedCohomology 0).carrier := by
  have : Finite X :=
    Scheme.Hom.finite_of_locallyQuasiFinite_toSpecField (X ↘ Spec (CommRingCat.of k₀))
  let : Fintype X.finitePoints := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_nontrivial_stalk_of_not_isZero F hF
  obtain ⟨γ, hγ⟩ := Module.End.exists_eigenvalue (F.stalk x).frobeniusEnd
  have hd := Scheme.Hom.degreeOver_ne_zero (X ↘ Spec (CommRingCat.of k₀)) x.2
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq γ (Nat.pos_of_ne_zero hd)
  have h0 := LinearMap.eval_inv_charpolyRev_eq_zero_of_hasEigenvalue _ hγ
    (FrobeniusModule.ne_zero_of_hasEigenvalue hγ)
  have h1 : Polynomial.eval β⁻¹ (F.compactlySupportedCohomology 0).frobeniusEnd.charpolyRev =
      0 := by
    rw [F.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite,
      Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
    rw [Polynomial.expand_eval, inv_pow, hβ, h0]
  obtain ⟨v, hv⟩ :=
    (LinearMap.hasEigenvalue_inv_of_eval_charpolyRev_eq_zero _ h1).exists_hasEigenvector
  exact ⟨v, 0, hv.2⟩

/-- On a `k₀`-scheme quasi-finite over `k₀`, a nonzero Weil sheaf has nonzero global sections
`Γ(X̄, F)`: these are `H^0 = H_c^0`, the scheme being finite, hence proper, over `k₀`. -/
theorem nontrivial_globalSections_of_not_isZero {F : WeilSheaf k₀ l X} (hF : ¬ IsZero F) :
    Nontrivial F.globalSections.carrier := by
  have h₁ := nontrivial_compactlySupportedCohomology_zero_of_not_isZero hF
  have : IsFinite (X ↘ Spec (CommRingCat.of k₀)) :=
    IsFinite.of_locallyQuasiFinite (X ↘ Spec (CommRingCat.of k₀))
  obtain ⟨e⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology
    (toComplex.obj F) 0
  have h₂ : Nontrivial (F.cohomology 0).carrier :=
    @Equiv.nontrivial _ _ e.toLinearEquiv.toEquiv.symm h₁
  set a := X ↘ Spec (CommRingCat.of k₀)
  let G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilCoefficients.{u} l :=
    ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
    Sheaf.Γ _ (WeilCoefficients.{u} l)
  let e' : G.obj ((WeilComplex.homologySheaf 0).obj ((WeilComplex.derivedLowerStar a).obj
      (toComplex.obj F))) ≅ (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X :=
    G.mapIso (homologySheafZeroDerivedLowerStarIso a _) ≪≫
      (ProEtale.globalSectionsLowerStarIso _ (Scheme.Hom.geometricFiberMap a (comp_over a _))).app
        F.obj.carrier.X
  exact @Equiv.nontrivial _ _ (WeilCoefficients.linearEquivOfIso e').toEquiv.symm h₂

/-- **Weil sheaves on a quasi-finite scheme are mixed.** Every Weil sheaf on a separated
`k₀`-scheme quasi-finite over `k₀` is `ι`-mixed: split off the image of `ℚ̄_ℓ(β) ⟶ F` for a
Frobenius eigenvector of `Γ(X̄, F)`, which is punctually pure, and induct on the total dimension
of the stalks (blueprint: `theorem-real-constructible-sheaves-are-mixed--1`, the dimension-zero
case: "a Jordan filtration of each invertible Frobenius operator gives pure factors"). -/
theorem isMixed_of_locallyQuasiFinite (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    F.IsMixed ι := by
  have : Finite X :=
    Scheme.Hom.finite_of_locallyQuasiFinite_toSpecField (X ↘ Spec (CommRingCat.of k₀))
  let : Fintype X.finitePoints := Fintype.ofFinite _
  suffices h : ∀ (n : ℕ) (F : WeilSheaf k₀ l X),
      ∑ x, Module.finrank (PadicAlgCl l) (F.stalk x).carrier = n → F.IsMixed ι from h _ F rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro F rfl
  by_cases hF : IsZero F
  · exact ⟨0, isMixedOfWeightsAtMost_of_isZero hF 0⟩
  have := nontrivial_globalSections_of_not_isZero hF
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue F.globalSections.frobeniusEnd
  have hβ₀ := FrobeniusModule.ne_zero_of_hasEigenvalue hβ
  obtain ⟨a, ha⟩ := hβ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at ha
  let b := Units.mk0 β hβ₀
  let u := homOfGlobalSection F b a ha.1
  have hu : u ≠ 0 := homOfGlobalSection_ne_zero F b a ha.1 ha.2
  have hI : ¬ IsZero (image u) := fun hI ↦ hu (by
    rw [← image.fac u, hI.eq_of_src (image.ι u) 0, comp_zero])
  obtain ⟨x₀, hx₀⟩ := exists_nontrivial_stalk_of_not_isZero (image u) hI
  have hlt : ∑ x, Module.finrank (PadicAlgCl l) ((cokernel (image.ι u)).stalk x).carrier <
      ∑ x, Module.finrank (PadicAlgCl l) (F.stalk x).carrier := by
    refine Finset.sum_lt_sum (fun x _ ↦ ?_) ⟨x₀, Finset.mem_univ _, ?_⟩
    · rw [← finrank_stalk_cokernel_add_finrank_stalk (image.ι u) x]
      exact Nat.le_add_right _ _
    · rw [← finrank_stalk_cokernel_add_finrank_stalk (image.ι u) x₀]
      exact Nat.lt_add_of_pos_right Module.finrank_pos
  obtain ⟨w, hQ⟩ := ih _ hlt _ rfl
  have hpure : (image u).IsPunctuallyPureOfWeight ι
      (0 + 2 * Real.logb (Nat.card k₀) ‖ι b‖) :=
    (isPunctuallyPureOfWeight_adicConstant.constantTwist rfl).of_epi (factorThruImage u)
  exact ⟨max _ w, (hpure.isMixedOfWeightsAtMost.mono_weight (le_max_left _ _)).of_mono_cokernel
    (image.ι u) (hQ.mono_weight (le_max_right _ _))⟩

end AlgebraicGeometry.WeilSheaf
