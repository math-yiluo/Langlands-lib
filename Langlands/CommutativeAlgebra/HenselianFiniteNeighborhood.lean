import Langlands.CommutativeAlgebra.HenselianSections
import Mathlib.RingTheory.Etale.QuasiFinite

/-! # Finite idempotent neighborhoods over a Henselian local ring -/

noncomputable section

universe u v

namespace Langlands.CommutativeAlgebra.HenselianFiniteNeighborhood

open TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An idempotent finite localization over an auxiliary algebra descends along
an algebra retraction. -/
theorem finite_away_of_retract
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (σ : A →ₐ[R] R)
    (e : A ⊗[R] S) [Module.Finite A (Localization.Away e)] :
    Module.Finite R (Localization.Away
      ((Algebra.TensorProduct.lift
        ((Algebra.ofId R S).comp σ) (AlgHom.id R S)
        (fun _ _ => Commute.all _ _)) e)) := by
  let ψ : A ⊗[R] S →ₐ[R] S :=
    Algebra.TensorProduct.lift ((Algebra.ofId R S).comp σ) (AlgHom.id R S)
      (fun _ _ => Commute.all _ _)
  have hψ : Function.Surjective ψ := by
    intro s
    exact ⟨1 ⊗ₜ[R] s, by simp [ψ]⟩
  let τ := Localization.awayMap ψ.toRingHom e
  have hτ : Function.Surjective τ := by
    exact IsLocalization.map_surjective_of_surjective _ _ _ hψ
  have hfinite : (τ.comp (algebraMap A (Localization.Away e))).Finite :=
    (RingHom.Finite.of_surjective τ hτ).comp
      (RingHom.finite_algebraMap.mpr inferInstance)
  have heq : τ.comp (algebraMap A (Localization.Away e)) =
      (algebraMap R (Localization.Away (ψ e))).comp σ.toRingHom := by
    ext a
    dsimp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply A (A ⊗[R] S) (Localization.Away e)]
    change τ (algebraMap (A ⊗[R] S) (Localization.Away e) (a ⊗ₜ[R] 1)) = _
    simp [τ, ψ, IsLocalization.Away.map,
      ← IsScalarTower.algebraMap_apply]
  rw [heq] at hfinite
  exact RingHom.finite_algebraMap.mp (RingHom.Finite.of_comp_finite hfinite)

/-- A prime above the closed point at which a finite-type algebra is
quasi-finite has a finite idempotent neighborhood. -/
theorem exists_idempotent_finite_away
    {R : Type u} {S : Type v} [CommRing R] [HenselianLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)]
    [Algebra.QuasiFiniteAt R q] :
    ∃ e : S, IsIdempotentElem e ∧ e ∉ q ∧ Module.Finite R (Localization.Away e) := by
  let p := IsLocalRing.maximalIdeal R
  obtain ⟨A, _, _, _, P, _, _, e, he, Q, _, _, hQq, heQ, hP, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let ρ : p.ResidueField ≃ₐ[R] P.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) hP
  let φ : A →ₐ[R] p.ResidueField :=
    ρ.symm.toAlgHom.comp (IsScalarTower.toAlgHom R A P.ResidueField)
  obtain ⟨σ, hσ⟩ := HenselianSections.exists_lift_of_etale
    (Ideal.algebraMap_residueField_surjective p) φ
  let ψ : A ⊗[R] S →ₐ[R] S :=
    Algebra.TensorProduct.lift ((Algebra.ofId R S).comp σ) (AlgHom.id R S)
      (fun _ _ => Commute.all _ _)
  have hσP : p.comap σ.toRingHom = P := by
    ext a
    change σ a ∈ p ↔ a ∈ P
    rw [← Ideal.algebraMap_residueField_eq_zero]
    change ((Algebra.ofId R p.ResidueField).comp σ) a = 0 ↔ a ∈ P
    rw [hσ]
    change ρ.symm (algebraMap A P.ResidueField a) = 0 ↔ a ∈ P
    rw [map_eq_zero_iff ρ.symm ρ.symm.injective,
      Ideal.algebraMap_residueField_eq_zero]
  let Q₀ := q.comap ψ.toRingHom
  have : Q₀.IsPrime := Ideal.comap_isPrime _ _
  have : Q₀.LiesOver P := by
    constructor
    change P = (q.comap ψ.toRingHom).comap (algebraMap A (A ⊗[R] S))
    rw [Ideal.comap_comap]
    have hcomp : ψ.toRingHom.comp (algebraMap A (A ⊗[R] S)) =
        (algebraMap R S).comp σ.toRingHom := by
      ext a
      simp [ψ]
    rw [hcomp, ← Ideal.comap_comap]
    change P = (q.under R).comap σ.toRingHom
    rw [← q.over_def p, hσP]
  have hQ₀q : Q₀.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
    dsimp [Q₀]
    rw [Ideal.comap_comap]
    convert q.comap_id
    ext s
    simp [ψ]
  have hQ₀ : Q₀ = Q :=
    Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP Q₀ Q (hQ₀q.trans hQq.symm)
  have hne : ψ e ∉ q := by
    change e ∉ Q₀
    rwa [hQ₀]
  exact ⟨ψ e, he.map ψ, hne, finite_away_of_retract σ e⟩

/-- Choose an actual idempotent whose principal open is finite over the base
and contains the specified closed-fibre prime. -/
def finiteNeighborhood
    {R : Type u} {S : Type v} [CommRing R] [HenselianLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)]
    [Algebra.QuasiFiniteAt R q] :
    {e : S // IsIdempotentElem e ∧ e ∉ q ∧ Module.Finite R (Localization.Away e)} :=
  ⟨Classical.choose (exists_idempotent_finite_away q),
    Classical.choose_spec (exists_idempotent_finite_away q)⟩

end Langlands.CommutativeAlgebra.HenselianFiniteNeighborhood
