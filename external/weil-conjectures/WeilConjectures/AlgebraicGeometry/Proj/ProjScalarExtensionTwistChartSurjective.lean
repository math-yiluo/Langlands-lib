/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionRealization

/-! The surjective half of the complete standard-chart scalar-extension comparison.

## References

* Stacks Project, Tags 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The prescribed scalar-extension twist map is surjective on a complete standard chart. -/
theorem scalarExtension_twistMap_chart_surjective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ)
    (η : (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j)
    (hη : ∀ (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U))
      (x : map ψ hψ ⁻¹ᵁ U),
      ((η.app (map ψ hψ ⁻¹ᵁ U)
        (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val)
    (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    Function.Surjective (η.app (basicOpen ℬ (ψ f))) := by
  classical
  have _compatibility := hβψ
  let V := basicOpen ℬ (ψ f)
  let P := (tensorPullback (map ψ hψ)).obj (twist 𝒜 j)
  have hpow (m : ℕ) (x : V) :
      (ψ f) ^ m ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 m
  let q (m : ℕ) (b : B) (x : V) :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal :=
    Localization.mk b ⟨(ψ f) ^ m, hpow m x⟩
  have lift (m : ℕ) (hj : 0 ≤ j + (m * n : ℕ)) (b : B)
      (hb : b ∈ ℬ (j + (m * n : ℕ)).toNat) :
      ∃ t : Γ(P, V), ∀ x : V, ((η.app V t).1 x).val = q m b x := by
    rw [hgraded] at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, ha, rfl⟩ := hb
      let z : LocalizedModule.Away f A :=
        LocalizedModule.mk a ⟨f ^ m, ⟨m, rfl⟩⟩
      have hz : z ∈ LocalizedModule.degreeZeroFractions
          (fun k : ℕ ↦ (𝒜 k : Set A))
          (fun k : ℕ ↦ {a : A | if 0 ≤ j + k then a ∈ 𝒜 (j + k).toNat
            else a = 0}) (Submonoid.powers f) := by
        refine ⟨m * n, a, ⟨f ^ m, ⟨m, rfl⟩⟩, ?_, ?_, rfl⟩
        · simpa only [Set.mem_ofPred_eq, ite_eq_left hj, SetLike.mem_coe] using ha
        · simpa using SetLike.pow_mem_graded m hf
      obtain ⟨s, hs⟩ := twist_fraction_realization 𝒜 j f z hz
      refine ⟨tensorPullbackSection (map ψ hψ) (twist 𝒜 j) (basicOpen 𝒜 f) s, ?_⟩
      intro x
      refine (hη (basicOpen 𝒜 f) s x).trans ?_
      have he := hs ⟨(map ψ hψ) x.1, x.2⟩
      change IsLocalization.map (M := Submonoid.powers f) _ (RingHom.id A) _
        (Localization.mk a (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) = _ at he
      simp only [Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply] at he
      rw [← he]
      have hfa : f ^ m ∈
          (Ideal.comap ψ.toRingHom x.1.asHomogeneousIdeal.toIdeal).primeCompl := by
        change ψ (f ^ m) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl
        simpa only [map_pow] using hpow m x
      calc
        _ = _ := Localization.localRingHom_mk'
          (I := Ideal.comap ψ.toRingHom x.1.asHomogeneousIdeal.toIdeal)
          x.1.asHomogeneousIdeal.toIdeal ψ.toRingHom rfl a ⟨f ^ m, hfa⟩
        _ = _ := by
          simp only [q, Localization.mk_eq_mk', map_pow]
          rfl
    | zero =>
      refine ⟨0, fun x ↦ ?_⟩
      rw [map_zero]
      change (0 : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = q m 0 x
      exact (Localization.mk_zero _).symm
    | add b c hb hc hbl hcl =>
      obtain ⟨t, ht⟩ := hbl
      obtain ⟨u, hu⟩ := hcl
      refine ⟨t + u, fun x ↦ ?_⟩
      rw [map_add]
      change ((η.app V t).1 x).val + ((η.app V u).1 x).val = _
      rw [ht, hu]
      exact Localization.add_mk_self _ _ _
    | smul c b hb hbl =>
      obtain ⟨t, ht⟩ := hbl
      have hc : algebraMap S B c ∈ ℬ 0 := by
        simpa only [Algebra.smul_def, mul_one] using
          (ℬ 0).smul_mem c (SetLike.one_mem_graded ℬ)
      let r : Γ(Proj ℬ, V) := awayToSection ℬ (ψ f)
        (HomogeneousLocalization.fromZeroRingHom ℬ _ ⟨algebraMap S B c, hc⟩)
      refine ⟨r • t, fun x ↦ ?_⟩
      rw [Hom.app_smul]
      change (r.1 x).val * ((η.app V t).1 x).val = _
      rw [ht]
      have hr : (r.1 x).val = Localization.mk (algebraMap S B c) 1 := by
        calc
          _ = _ := ProjectiveSpectrum.Proj.awayToSection_apply ℬ (ψ f)
            (HomogeneousLocalization.fromZeroRingHom ℬ _ ⟨algebraMap S B c, hc⟩) x
          _ = _ := by
            simp only [HomogeneousLocalization.val_fromZeroRingHom,
              Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
            rfl
      rw [hr]
      simpa only [q, Algebra.smul_def, one_mul] using
        (Localization.mk_mul (algebraMap S B c) b 1
          ⟨(ψ f) ^ m, hpow m x⟩)
  intro s
  by_cases hV : Nonempty V
  · obtain ⟨z, hz, hs⟩ := twist_fraction_descent ℬ j (ψ f) n hn (ψ.map_mem hf) s
    obtain ⟨d, b, den, hb, hd, rfl⟩ := hz
    obtain ⟨m, hm⟩ := den.2
    have hden : (den : B) ≠ 0 := by
      intro hzero
      obtain ⟨x⟩ := hV
      have hx : (den : B) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
        (Submonoid.powers_le.mpr x.2) den.2
      exact hx (hzero ▸ x.1.asHomogeneousIdeal.toIdeal.zero_mem)
    have hdegree : d = m * n := DirectSum.degree_eq_of_mem_mem ℬ hd
      (by simpa [← hm] using SetLike.pow_mem_graded m (ψ.map_mem hf))
      hden
    subst d
    by_cases hj : 0 ≤ j + (m * n : ℕ)
    · obtain ⟨t, ht⟩ := lift m hj b (by simpa only [Set.mem_ofPred_eq, ite_eq_left hj] using hb)
      refine ⟨t, Subtype.ext (funext fun x ↦ Subtype.ext ?_)⟩
      rw [ht]
      have he := hs x
      change IsLocalization.map _ (RingHom.id B) _ (Localization.mk b den) = _ at he
      rw [← he]
      simp only [Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply, q, hm]
    · have hb0 : b = 0 := by simpa only [Set.mem_ofPred_eq, ite_eq_right hj] using hb
      refine ⟨0, Subtype.ext (funext fun x ↦ Subtype.ext ?_)⟩
      rw [map_zero]
      change (0 : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
      rw [← hs x, hb0]
      change 0 = IsLocalization.map _ (RingHom.id B) _ (Localization.mk 0 den)
      rw [Localization.mk_zero, map_zero]
  · refine ⟨0, Subtype.ext (funext fun x ↦ ?_)⟩
    exact (hV ⟨x⟩).elim

end AlgebraicGeometry.Proj
