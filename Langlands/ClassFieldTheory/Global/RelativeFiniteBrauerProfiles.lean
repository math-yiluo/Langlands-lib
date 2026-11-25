import Langlands.ClassFieldTheory.Global.InvariantProof

/-!
# Finite profiles in relative field-unit cohomology

A finitely supported family of finite local invariants with the local denominators of `L / F` and
sum zero comes from a class of `H²(Gal(L/F), Lˣ)` whose archimedean invariants all vanish
(`exists_relativeCohomology_of_finiteInvariants_archimedean`; without the archimedean part,
`exists_relativeCohomology_of_finiteInvariants`). An idèle class of total invariant zero lies in the
image of `H²(Gal(L/F), Lˣ)` (`ideleQuotientCohomologyMap_eq_zero_of_total_eq_zero`).
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Global

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Local
open FundamentalClass
open scoped FiniteExtension

universe u

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L]
  [Algebra F L] [IsGalois F L]

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hCF : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)

/-- An idèle class of total invariant zero lies in the image of `H²(Gal(L/F), Lˣ)`. -/
theorem ideleQuotientCohomologyMap_eq_zero_of_total_eq_zero
    (c : relativeIdeleCohomology F L 2)
    (hc : totalIdeleInvariantMaps I (fun p _ => (hCF p).1.2.1) F L c = 0) :
    ideleQuotientCohomologyMap F L 2 c = 0 := by
  have hImages (p : ℕ) [Fact p.Prime] : (I p).RelativeImages := (hCF p).1.2.1
  have hInflation (p : ℕ) [Fact p.Prime] : (I p).InflationCompatibility := (hCF p).1.2.2.1
  have hRestriction (p : ℕ) [Fact p.Prime] : (I p).RelativeRestriction := (hCF p).1.2.2.2
  let s := totalIdeleInvariantMaps I hImages
  have hker := totalIdeleInvariantMaps_killsQuotientKernel_of_h1 I hImages ideleClassH1Vanishing hCF
  have hInf := totalIdeleInvariantMaps_inflation_of_inflationCompatibility I hInflation hImages
  have hRes := totalIdeleInvariantMaps_restriction_of_localLaws I hRestriction hInflation hImages
  have hcyc := totalIdeleInvariantMaps_cyclicRange I hImages cyclicPrimePowerLocalDegreeStatement
  have hi := assembledIdeleClassInvariantMaps_images s hker hInf hRes hcyc
    ideleClassGaloisDescent ideleClassH1Vanishing ideleClassH2OrderBound
  apply (hi F L).1
  rw [assembledIdeleClassInvariantMaps_apply_quotient, map_zero]
  exact hc

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

/-- A finitely supported family of finite invariants with the appropriate
local denominators and sum zero lifts to a relative field-unit class. -/
def RelativeFiniteBrauerProfileStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
  ∀ (S : Finset (Langlands.Global.FinitePlace F)) (a : Langlands.Global.FinitePlace F →
    RationalModIntegers), (∀ v ∉ S, a v = 0) →
    (∀ v ∈ S, a v ∈ denominatorSubgroup
      (Module.finrank (FiniteCompletion F v) (FiniteCompletion L (placeAbove L v).val))) →
    (∑ v ∈ S, a v = 0) →
    ∃ x : relativeCohomology F L 2, ∀ v : Langlands.Global.FinitePlace F,
      Reciprocity.finiteLocalInvariant v (placeAbove L v).val I x = a v

/-- **Finite profiles with trivial archimedean invariants.** A finitely supported family of finite
invariants with the local denominators of `L / F` and sum zero comes from a class of
`H²(Gal(L/F), Lˣ)` whose archimedean invariants all vanish: the class is the preimage of a sum of
local sections of the idèle cohomology at finite places, on which the archimedean idèle invariants
vanish. -/
theorem exists_relativeCohomology_of_finiteInvariants_archimedean
    (hCF : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (S : Finset (Langlands.Global.FinitePlace F))
    (a : Langlands.Global.FinitePlace F → RationalModIntegers)
    (ha₀ : ∀ v ∉ S, a v = 0)
    (ha : ∀ v ∈ S, a v ∈ denominatorSubgroup
      (Module.finrank (FiniteCompletion F v) (FiniteCompletion L (placeAbove L v).val)))
    (hsum : ∑ v ∈ S, a v = 0) :
    ∃ x : relativeCohomology F L 2,
      (∀ v, Reciprocity.finiteLocalInvariant v (placeAbove L v).val I x = a v) ∧
        ∀ u : NumberField.InfinitePlace L, Reciprocity.archimedeanInvariant u x = 0 := by
  classical
  have hImages (p : ℕ) [Fact p.Prime] : (I p).RelativeImages := (hCF p).1.2.1
  let w := placeAbove (K := F) L
  let : ∀ v : Langlands.Global.FinitePlace F,
      Fintype ((L ≃ₐ[F] L) ⧸ (decompositionHom v (w v).val).range) := fun _ => Fintype.ofFinite _
  let y (v : S) : denominatorSubgroup
      (Module.finrank (FiniteCompletion F v.val) (FiniteCompletion L (w v.val).val)) :=
    ⟨a v.val, ha v.val v.property⟩
  let lift (v : S) := finiteIdeleInvariantLift I hImages v.val (w v.val).val (y v)
  have hlift (v : S) : totalIdeleInvariantMaps I hImages F L (lift v) = a v.val := by
    change totalIdeleInvariantMaps I hImages F L (ideleLocalSection v.val (w v.val).val 2
      (((I (residuePrime v.val)).relativeInvariantEquiv (hImages _) (padicField v.val)
        ((w v.val).val.adicCompletion L)).symm (y v))) = _
    rw [totalIdeleInvariantMaps_ideleLocalSection, InvariantFamily.relativeInvariantEquiv_symm_apply]
  have htotal : totalIdeleInvariantMaps I hImages F L (∑ v : S, lift v) = 0 := by
    simp only [map_sum, hlift]
    change (∑ v ∈ S.attach, a v.val) = 0
    rwa [Finset.sum_attach]
  obtain ⟨x, hx⟩ := (ideleQuotientCohomologyMap_eq_zero_iff F L 2 _).mp
    (ideleQuotientCohomologyMap_eq_zero_of_total_eq_zero I hCF (∑ v : S, lift v) htotal)
  refine ⟨x, fun p => ?_, fun u => ?_⟩
  · rw [← finiteIdeleInvariant_principal, hx, map_sum]
    have hvanish (v : S) (h : p ≠ v.val) :
        finiteIdeleInvariant I p (w p).val (lift v) = 0 :=
      finiteIdeleInvariant_ideleLocalSection_of_base_ne I v.val p (w v.val).val (w p).val h _
    by_cases hp : p ∈ S
    · let p' : S := ⟨p, hp⟩
      have hp' : ∀ v : S, v ≠ p' → p ≠ v.val :=
        fun v hn he => hn (Subtype.ext he.symm)
      rw [Finset.sum_eq_single p' (fun v _ hv => hvanish v (hp' v hv)) (by simp)]
      exact finiteIdeleInvariant_finiteIdeleInvariantLift I hImages p'.val (w p'.val).val (y p')
    · rw [Finset.sum_eq_zero (fun v _ => hvanish v (fun h => hp (h.symm ▸ v.property))), ha₀ p hp]
  · rw [← archimedeanIdeleInvariant_principalIdeleCohomologyMap, hx, map_sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    change archimedeanIdeleInvariant F u (ideleLocalSection v.val (w v.val).val 2
      (((I (residuePrime v.val)).relativeInvariantEquiv (hImages _) (padicField v.val)
        ((w v.val).val.adicCompletion L)).symm (y v))) = 0
    exact archimedeanIdeleInvariant_ideleLocalSection v.val (w v.val).val u _

/-- The finite-profile statement, from `exists_relativeCohomology_of_finiteInvariants_archimedean`
(forgetting the archimedean invariants). -/
theorem exists_relativeCohomology_of_finiteInvariants :
    RelativeFiniteBrauerProfileStatement (F := F) (L := L) I := by
  intro hCF S a ha₀ ha hsum
  obtain ⟨x, hx, -⟩ :=
    exists_relativeCohomology_of_finiteInvariants_archimedean I hCF S a ha₀ ha hsum
  exact ⟨x, hx⟩

end Langlands.ClassFieldTheory.Global
