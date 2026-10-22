import Langlands.LocalField.DVRDegreeStatement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module

namespace Langlands.LocalField

open Module Submodule

private theorem quotient_dimension_bound
    (R k K V M Q : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field k] [Algebra R k] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [Module.Finite K V]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    [AddCommGroup Q] [Module R Q] [Module k Q] [IsScalarTower R k Q]
    (f : M →ₗ[R] Q) (hf : Function.Surjective f)
    (g : M →ₗ[R] V) (hg : Function.Injective g) :
    finrank k Q ≤ finrank K V := by
  classical
  by_cases hQ : Module.Finite k Q
  · let := hQ
    let bQ := Module.Free.chooseBasis k Q
    choose v hv using fun i ↦ hf (bQ i)
    let N := Submodule.span R (Set.range v)
    have : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range v)
    let bN := Module.Free.chooseBasis R N
    let h : N →ₗ[R] Q := f.comp N.subtype
    have hs : Submodule.span k (Set.range (fun j ↦ h (bN j))) = ⊤ := by
      apply top_unique
      rw [← bQ.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      let x : N := ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
      have hx : h x = bQ i := hv i
      rw [← hx, ← bN.sum_repr x, map_sum]
      apply Submodule.sum_mem
      intro j _
      rw [map_smul]
      exact (Submodule.span k (Set.range (fun j ↦ h (bN j)))).restrictScalars R |>.smul_mem _
        (Submodule.subset_span ⟨j, rfl⟩)
    have hi := bN.linearIndependent.map' (g.comp N.subtype) (LinearMap.ker_eq_bot.mpr (hg.comp Subtype.val_injective))
    have hiK := (LinearIndependent.iff_fractionRing R K).mp hi
    exact (finrank_le_of_span_eq_top hs).trans hiK.fintype_card_le_finrank
  · rw [Module.finrank_of_not_finite hQ]
    exact Nat.zero_le _

attribute [local instance] Ideal.Quotient.field

open IsLocalRing in
private theorem ramification_inertia_eq_quotient_finrank
    (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (maximalIdeal S).ramificationIdx R * (maximalIdeal S).inertiaDeg R =
      finrank (R ⧸ maximalIdeal R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  let p := maximalIdeal R
  let q := maximalIdeal S
  let Sq := Localization.AtPrime q
  let e : S ≃ₐ[S] Sq := IsLocalization.atUnits S q.primeCompl
    (fun x ↦ by simpa [q] using! fun a ↦ a)
  have he : Function.Surjective (algebraMap S Sq) := e.surjective
  have heq : (e : S →+* Sq) = algebraMap S Sq := by
    ext x
    exact e.commutes x
  let eqQ := Ideal.quotientEquivAlg (p.map (algebraMap R S))
    (p.map (algebraMap R Sq)) e
    (by rw [Ideal.map_map, heq, ← IsScalarTower.algebraMap_eq])
  have hr : q.ramificationIdx R =
      (Module.length S (S ⧸ p.map (algebraMap R S))).toNat := by
    rw [Ideal.ramificationIdx_eq p q,
      ← Module.length_eq_of_surjective (M := Sq ⧸ p.map (algebraMap R Sq)) he,
      ← eqQ.toLinearEquiv.length_eq]
  have hi : q.inertiaDeg R = finrank (ResidueField R) (ResidueField S) :=
    Ideal.inertiaDeg_eq_of_isMaximal p q
  change q.ramificationIdx R * q.inertiaDeg R = _
  rw [hr, hi]
  have hl := IsLocalRing.length_restrictScalars R S (S ⧸ p.map (algebraMap R S))
  have hq := Module.length_eq_of_surjective
    (R := R ⧸ p) (M := S ⧸ p.map (algebraMap R S))
    (Ideal.Quotient.mk_surjective)
  rw [hq] at hl
  apply_fun ENat.toNat at hl
  simpa [Module.length_eq_rank, ENat.toNat_mul, Module.finrank] using hl.symm

universe uR uS uK uL

/-- The ramification-inertia lower bound for a local extension of DVRs. -/
theorem dvrDegreeLowerBound : DVRDegreeLowerBound.{uR, uS, uK, uL} := by
  intro R S K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans K
  let g : S →ₗ[R] L := (IsScalarTower.toAlgHom R S L).toLinearMap
  have hg : Function.Injective g := IsFractionRing.injective S L
  have : Module.IsTorsionFree R S := hg.moduleIsTorsionFree g (fun r x ↦ g.map_smul r x)
  rw [ramification_inertia_eq_quotient_finrank]
  let p := IsLocalRing.maximalIdeal R
  let Q := S ⧸ p.map (algebraMap R S)
  let f : S →ₗ[R] Q := (IsScalarTower.toAlgHom R S Q).toLinearMap
  exact quotient_dimension_bound R (R ⧸ p) K L S Q f
    Ideal.Quotient.mk_surjective g hg

end Langlands.LocalField
