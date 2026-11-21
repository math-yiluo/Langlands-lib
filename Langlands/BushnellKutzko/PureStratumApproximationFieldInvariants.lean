import Langlands.BushnellKutzko.ElementFieldInvariants
import Langlands.BushnellKutzko.CorestrictionIntegers

/-! # Field invariants under embeddings and isomorphisms

These comparisons use the actual integral closures and invariants used by the stratum
approximation statement.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uK

private theorem length_quotient_eq_inertiaDeg {R : Type uF} {S : Type uE} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal]
    [q.LiesOver p] :
    (Module.length R (S ⧸ q)).toNat = q.inertiaDeg R := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal p q]
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  rw [Module.length_eq_of_surjective (R := R ⧸ p) (S := R) (M := S ⧸ q)
    Ideal.Quotient.mk_surjective]
  simp [Module.length_eq_rank, Module.finrank]

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {K : Type uK} [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The ramification index is the prime ideal ramification index of the extension integers. -/
theorem subfieldRamificationIndex_eq_ramificationIdx :
    subfieldRamificationIndex F E =
      (IsLocalRing.maximalIdeal (subfieldIntegers F E)).ramificationIdx 𝒪[F] := by
  unfold subfieldRamificationIndex
  rw [subfieldMaximalIdeal_eq F E]

/-- The residue degree computed as a length equals the inertia degree of the same ideal. -/
theorem subfieldResidueDegree_eq_inertiaDeg :
    subfieldResidueDegree F E =
      (IsLocalRing.maximalIdeal (subfieldIntegers F E)).inertiaDeg 𝒪[F] := by
  let O := subfieldIntegers F E
  let p : Ideal 𝒪[F] := 𝓂[F]
  let q := IsLocalRing.maximalIdeal O
  let : Algebra.IsIntegral 𝒪[F] O := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  let : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  let : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  let : q.LiesOver p :=
    ⟨(IsLocalRing.eq_maximalIdeal (inferInstance : (q.under 𝒪[F]).IsMaximal)).symm⟩
  unfold subfieldResidueDegree subfieldResidueRing
  rw [subfieldMaximalIdeal_eq F E]
  exact length_quotient_eq_inertiaDeg p q

/-- Embedding one finite extension of a nonarchimedean local field in another gives both
divisibilities. Every hypothesis is a binder of this definition, not a section variable. -/
def SubfieldInvariantsEmbeddingStatement (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]
    (K : Type uK) [Field K] [Algebra F K] [FiniteDimensional F K] : Prop :=
  ∀ (_ : E →ₐ[F] K),
    subfieldRamificationIndex F E ∣ subfieldRamificationIndex F K ∧
      subfieldResidueDegree F E ∣ subfieldResidueDegree F K

/-- Restrict the embedding to integral closures and use the two ideal tower formulas. -/
theorem subfieldInvariantsEmbedding : SubfieldInvariantsEmbeddingStatement F E K := by
  intro f
  let R := 𝒪[F]
  let S := subfieldIntegers F E
  let T := subfieldIntegers F K
  let g : S →ₐ[R] T := (f.restrictScalars R).mapIntegralClosure
  let : Algebra S T := g.toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  let : Algebra.IsIntegral R T := inferInstanceAs
    (Algebra.IsIntegral R (integralClosure R K))
  let : Algebra.IsIntegral S T := Algebra.IsIntegral.tower_top (R := R)
  have hg : Function.Injective (algebraMap S T) := by
    intro x y h
    apply Subtype.ext
    apply f.injective
    exact congrArg (fun z : T => (z : K)) h
  let : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr hg
  let : Module.IsTorsionFree S T := Module.IsTorsionFree.trans_faithfulSMul S T T
  let q := IsLocalRing.maximalIdeal S
  let r := IsLocalRing.maximalIdeal T
  let : r.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  let : r.LiesOver q :=
    ⟨(IsLocalRing.eq_maximalIdeal (inferInstance : (r.under S).IsMaximal)).symm⟩
  rw [subfieldRamificationIndex_eq_ramificationIdx, subfieldRamificationIndex_eq_ramificationIdx,
    subfieldResidueDegree_eq_inertiaDeg, subfieldResidueDegree_eq_inertiaDeg]
  exact ⟨Ideal.ramificationIdx_below_dvd (R := R) q r, Ideal.inertiaDeg_below_dvd (R := R) q r⟩

/-- The invariants are unchanged by an `F`-algebra isomorphism of fields. -/
theorem subfieldInvariants_of_algEquiv (f : E ≃ₐ[F] K) :
    subfieldRamificationIndex F E = subfieldRamificationIndex F K ∧
      subfieldResidueDegree F E = subfieldResidueDegree F K := by
  have h₁ := subfieldInvariantsEmbedding f.toAlgHom
  have h₂ := subfieldInvariantsEmbedding f.symm.toAlgHom
  exact ⟨Nat.dvd_antisymm h₁.1 h₂.1, Nat.dvd_antisymm h₁.2 h₂.2⟩

end Langlands.BushnellKutzko.PureApproximation
