import Langlands.Global.Factors.WeilPoleRegionUnitaryProof
import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterProof

/-! # From the two cuspidal cases to unitary weak base change of singleton data -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

section CentralCharacter

variable {F : Type uF} [Field F] [NumberField F]

local instance singletonBaseChangeRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance singletonBaseChangeContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance singletonBaseChangeFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance singletonBaseChangeFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance singletonBaseChangeStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance singletonBaseChangeRealizationGroup {n : ℕ} (R : OperatorRealization F n) :
    AddCommGroup R.Space :=
  Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The central character of an actual unitarizable cuspidal realization is unitary. -/
theorem CuspidalOperatorRealization.hasUnitaryCentralCharacter_of_isUnitarizable
    (S : CuspidalOperatorRealization F r) (hS : S.realization.IsUnitarizable) :
    ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S := by
  obtain ⟨χ, hχ⟩ : ∃ χ : HeckeCharacter F, S.HasCentralCharacter χ :=
    (S.realization.existsUnique_hasCentralCharacter S.irreducible).exists
  obtain ⟨b⟩ := hS
  obtain ⟨f, hf⟩ := exists_ne (0 : S.Space)
  have local_norm (v : FinitePlace F) (a : (FiniteCompletion F v)ˣ) :
      ‖(χ.finiteComponent v a : ℂ)‖ = 1 := by
    let g := Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a
    let z : ℂ := χ.finiteComponent v a
    have hmem : finiteIdeleInclusion F v a ∈ S.realization.centralCharacterSubgroup χ :=
      (S.realization.mem_centralCharacterSubgroup χ _).mpr fun w x =>
        S.realization.centralCharacter_evaluate χ hχ w _ x
    have hscalar : S.realization.localRepresentation v g f = z • f :=
      (S.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff χ v a).mp hmem f
    have hinner : b.finiteForm.inner (S.realization.localRepresentation v g f)
        (S.realization.localRepresentation v g f) = b.finiteForm.inner f f :=
      b.finiteForm.invariant (localInclusion F (r + 1) v g) f f
    exact Langlands.Global.WeilPoleRegionUnitary.norm_eq_one_of_inner_smul_self b.finiteForm.toInnerProductCore (c := z) hf
      ((congrArg₂ b.finiteForm.inner hscalar hscalar).symm.trans hinner)
  let modulus : Ideles F →* ℝ :=
    normHom.toMonoidHom.comp ((Units.coeHom ℂ).comp χ.onIdeles.toMonoidHom)
  have hclosed : IsClosed (modulus.ker : Set (Ideles F)) := by
    change IsClosed {a : Ideles F | ‖(χ.onIdeles a : ℂ)‖ = 1}
    exact isClosed_eq (Units.continuous_val.comp χ.onIdeles.continuous).norm continuous_const
  have htop : modulus.ker = ⊤ := by
    apply IdeleDensity.eq_top_of_isClosed modulus.ker ∅ hclosed
    · intro a
      change ‖(χ.onIdeles (diagonalUnits F a) : ℂ)‖ = 1
      simp
    · intro v _ a
      exact local_norm v a
  refine ⟨χ, ?_, hχ⟩
  intro c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  have ha : a ∈ modulus.ker := htop.symm ▸ Subgroup.mem_top a
  exact ha

end CentralCharacter

namespace Unramified

open CuspidalOperatorRealization IsobaricData

/-- The two prime cyclic cuspidal lift cases give weak base change of a
unitary singleton as a unitary isobaric datum. -/
def CyclicPrimeSingletonBaseChangeReductionStatement (F : Type uF) (E : Type uE)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)] : Prop :=
  CyclicPrimeIsobaricLiftStatement.{uF, uE, uV, uW} →
  CyclicPrimeIsobaricSelfTwistStatement.{uF, uE, uV, uW} →
  (Module.finrank F E).Prime →
  ∀ c : PositiveRankCuspidalClass F, (ofCuspidal c).IsUnitary →
    ∃ D : IsobaricData E, D.IsUnitary ∧
      IsWeakBaseChangeOf.{uF, uE, uV, uW} D (ofCuspidal c)

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- Given Arthur–Clozel's two isobaric lift results for a unitary cuspidal
source, any unitary singleton has a unitary weak base change. -/
theorem cyclicPrimeSingletonBaseChange_of_cuspidal :
    CyclicPrimeSingletonBaseChangeReductionStatement.{uF, uE, uV, uW} F E := by
  intro hLift hSelfTwist hprime c hc
  classical
  let _ : Fact (Module.finrank F E).Prime := ⟨hprime⟩
  let _ : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank F E)
  obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter F E).1
  rcases c with ⟨r, c⟩
  obtain ⟨S, rfl⟩ := c.exists_representative
  have hun : S.realization.IsUnitarizable := isUnitary_ofCuspidal.mp hc
  have hcentral := S.hasUnitaryCentralCharacter_of_isUnitarizable hun
  by_cases htwist : IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass
  · obtain ⟨m, d, _, _, hD, hbc⟩ := hSelfTwist F E hprime η hη r S hcentral htwist
    exact ⟨galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank d), hD, (hbc _ hD).2 rfl⟩
  · obtain ⟨d, hD, hbc⟩ := hLift F E hprime η hη r S hcentral htwist
    exact ⟨ofCuspidal (PositiveRankCuspidalClass.ofFixedRank d), hD, (hbc _ hD).2 rfl⟩

end Unramified

end Langlands.Automorphic
