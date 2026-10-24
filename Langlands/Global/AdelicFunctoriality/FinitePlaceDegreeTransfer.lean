import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.AdelicFunctoriality.Inclusion
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! # Degree-weighted transfer of finitely supported families at finite places -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension Classical

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The sum of the completed degrees above one finite place is the global degree. -/
theorem finiteLocalDegree_sum (p : HeightOneSpectrum (𝓞 K)) :
    (∑ q : FinitePlacesAbove L p,
      Module.finrank (p.adicCompletion K) (q.1.adicCompletion L)) = Module.finrank K L := by
  simp only [localDegree_eq]
  exact finitePlacesAbove_sum_ramification_inertia p

variable {A : Type w} [AddCommMonoid A]

/-- Transfer a finitely supported family to upper finite places, weighted by completed degrees. -/
def finitePlaceDegreeTransfer :
    (HeightOneSpectrum (𝓞 K) →₀ A) →+ (HeightOneSpectrum (𝓞 L) →₀ A) :=
  Finsupp.liftAddHom fun p => ∑ q : FinitePlacesAbove L p,
    Module.finrank (p.adicCompletion K) (q.1.adicCompletion L) • Finsupp.singleAddHom q.1

@[simp] theorem finitePlaceDegreeTransfer_single (p : HeightOneSpectrum (𝓞 K)) (a : A) :
    finitePlaceDegreeTransfer (L := L) (Finsupp.single p a) =
      ∑ q : FinitePlacesAbove L p,
        Finsupp.single q.1 (Module.finrank (p.adicCompletion K) (q.1.adicCompletion L) • a) := by
  simp [finitePlaceDegreeTransfer]

/-- Evaluation of a transferred single at a place lying above its index. -/
theorem finitePlaceDegreeTransfer_single_apply (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver p.asIdeal] (a : A) :
    finitePlaceDegreeTransfer (L := L) (Finsupp.single p a) q =
      Module.finrank (p.adicCompletion K) (q.adicCompletion L) • a := by
  rw [finitePlaceDegreeTransfer_single, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (⟨q, hq⟩ : FinitePlacesAbove L p)]
  · exact Finsupp.single_eq_same
  · intro r _ hr
    apply Finsupp.single_eq_of_ne
    intro he
    exact hr (Subtype.ext he.symm)
  · simp

/-- A transferred single vanishes at a place lying over a different base place. -/
theorem finitePlaceDegreeTransfer_single_apply_of_ne (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (h : p ≠ q.under (𝓞 K)) (a : A) :
    finitePlaceDegreeTransfer (L := L) (Finsupp.single p a) q = 0 := by
  rw [finitePlaceDegreeTransfer_single, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro r _
  apply Finsupp.single_eq_of_ne
  intro he
  have hr := r.2
  have : q.asIdeal.LiesOver p.asIdeal := he ▸ hr
  exact h (HeightOneSpectrum.ext (Ideal.over_def q.asIdeal p.asIdeal))

/-- The transferred coordinate is the lower coordinate times the actual completed degree. -/
theorem finitePlaceDegreeTransfer_apply (f : HeightOneSpectrum (𝓞 K) →₀ A)
    (q : HeightOneSpectrum (𝓞 L)) :
    finitePlaceDegreeTransfer (L := L) f q =
      Module.finrank ((q.under (𝓞 K)).adicCompletion K) (q.adicCompletion L) •
        f (q.under (𝓞 K)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, smul_add]
  | single p a =>
    by_cases h : p = q.under (𝓞 K)
    · subst p
      rw [finitePlaceDegreeTransfer_single_apply, Finsupp.single_eq_same]
    · rw [finitePlaceDegreeTransfer_single_apply_of_ne p q h, Finsupp.single_eq_of_ne (Ne.symm h),
        smul_zero]

/-- Coordinate form at any specified lower place. -/
theorem finitePlaceDegreeTransfer_apply_of_liesOver (f : HeightOneSpectrum (𝓞 K) →₀ A)
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] :
    finitePlaceDegreeTransfer (L := L) f q =
      Module.finrank (p.adicCompletion K) (q.adicCompletion L) • f p := by
  have hp : p = q.under (𝓞 K) := HeightOneSpectrum.ext (Ideal.over_def q.asIdeal p.asIdeal)
  subst p
  exact finitePlaceDegreeTransfer_apply f q

/-- Sum of a finitely supported family indexed by finite places. -/
def finitePlaceSum : (HeightOneSpectrum (𝓞 K) →₀ A) →+ A :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id A

omit [NumberField K] in
@[simp] theorem finitePlaceSum_single (p : HeightOneSpectrum (𝓞 K)) (a : A) :
    finitePlaceSum (Finsupp.single p a) = a :=
  Finsupp.liftAddHom_apply_single _ _ _

omit [NumberField K] in
/-- The additive sum map agrees with the finite-support sum of the coordinate function. -/
theorem finitePlaceSum_eq_finsum (f : HeightOneSpectrum (𝓞 K) →₀ A) :
    finitePlaceSum f = ∑ᶠ p, f p := by
  change (∑ p ∈ f.support, f p) = _
  symm
  apply finsum_eq_sum_of_support_subset
  intro p hp
  exact Finsupp.mem_support_iff.mpr hp

/-- Degree-weighted transfer multiplies the total sum by the global field degree. -/
theorem finitePlaceSum_degreeTransfer (f : HeightOneSpectrum (𝓞 K) →₀ A) :
    finitePlaceSum (finitePlaceDegreeTransfer (L := L) f) =
      Module.finrank K L • finitePlaceSum f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, smul_add]
  | single p a =>
    rw [finitePlaceDegreeTransfer_single, map_sum]
    simp only [finitePlaceSum_single]
    rw [← Finset.sum_smul, finiteLocalDegree_sum]

/-- Finite-support sum form of the degree-weighted transfer formula. -/
theorem finsum_finitePlaceDegreeTransfer (f : HeightOneSpectrum (𝓞 K) →₀ A) :
    (∑ᶠ q, finitePlaceDegreeTransfer (L := L) f q) =
      Module.finrank K L • ∑ᶠ p, f p := by
  rw [← finitePlaceSum_eq_finsum, ← finitePlaceSum_eq_finsum, finitePlaceSum_degreeTransfer]

end Langlands.Global.AdelicFunctoriality
