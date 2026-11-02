import Langlands.AlgebraicGeometry.SmoothAlgebraDifferentialSliceProof
import Langlands.AlgebraicGeometry.AffineLocalizedQuotientPullback

/-! # Affine slices from transverse differential equations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Algebra TensorProduct

namespace Langlands.AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local instance (q : Spec (CommRingCat.of B)) : q.asIdeal.IsPrime :=
  (q : PrimeSpectrum B).isPrime

/-- Choose equations in an allowed ideal of the target whose pullbacks cut
out an etale quotient of a principal open of the smooth source. -/
theorem exists_ideal_etale_quotient_of_residue_span
    [Algebra.Smooth A B] (θ : A →+* B) (p : Ideal A)
    (q : Ideal B) [q.IsPrime]
    (hC : Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime q))
      (Set.range (fun x : θ '' (p : Set A) ↦
        (1 : IsLocalRing.ResidueField (Localization.AtPrime q)) ⊗ₜ[Localization.AtPrime q]
          KaehlerDifferential.D A (Localization.AtPrime q)
            (algebraMap B (Localization.AtPrime q) x))) = ⊤) :
    ∃ (I : Ideal A), I.FG ∧ I ≤ p ∧
      ∃ (g : B), g ∉ q ∧ Algebra.Etale A
        ((Localization.Away g) ⧸ I.map ((algebraMap B (Localization.Away g)).comp θ)) := by
  obtain ⟨ι, hι, f, hf, g, hg, he⟩ :=
    exists_notMem_etale_quotient_span_of_residue_span q (θ '' (p : Set A)) hC
  have hex : ∀ i, ∃ a, a ∈ p ∧ θ a = f i := hf
  choose a ha haf using hex
  let I : Ideal A := Ideal.span (Set.range a)
  refine ⟨I, Submodule.fg_span (Set.finite_range a), ?_, g, hg, ?_⟩
  · exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ha i)
  · have hmap : I.map ((algebraMap B (Localization.Away g)).comp θ) =
        Ideal.span (Set.range (fun i ↦ algebraMap B (Localization.Away g) (f i))) := by
      simp only [I, Ideal.map_span, ← Set.range_comp, Function.comp_def, RingHom.comp_apply]
      simp only [haf]
    rw [hmap]
    exact he

/-- Residue-cotangent spanning cuts out a finite affine slice whose pullback
has a formally etale stalk above the chosen prime. -/
theorem exists_affineSlice_formallyEtale_of_residue_span
    [Algebra.Smooth A B] (θ : A →+* B) (p : Ideal A)
    (q : Spec (CommRingCat.of B)) (hpq : p ≤ q.asIdeal.comap θ)
    (hC : Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (Set.range (fun x : θ '' (p : Set A) ↦
        (1 : IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) ⊗ₜ[Localization.AtPrime q.asIdeal]
          KaehlerDifferential.D A (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) x))) = ⊤) :
    ∃ (I : Ideal A), I.FG ∧ I ≤ p ∧
      ∃ b : (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom θ)) : Scheme.{u}),
        (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          (Spec.map (CommRingCat.ofHom θ))) b = q ∧
        ((pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap b).hom.FormallyEtale := by
  obtain ⟨I, hIfg, hIp, g, hg, he⟩ :=
    exists_ideal_etale_quotient_of_residue_span θ p q.asIdeal hC
  refine ⟨I, hIfg, hIp, ?_⟩
  apply exists_formallyEtale_stalk_affinePullback (algebraMap A B) θ I g q hg (hIp.trans hpq)
  let := he
  change ((algebraMap (Localization.Away g)
    ((Localization.Away g) ⧸ I.map ((algebraMap B (Localization.Away g)).comp θ))).comp
      ((algebraMap B (Localization.Away g)).comp (algebraMap A B))).Etale
  rw [← IsScalarTower.algebraMap_eq A B (Localization.Away g),
    ← IsScalarTower.algebraMap_eq, RingHom.etale_algebraMap]
  exact he

end Langlands.AlgebraicGeometry
