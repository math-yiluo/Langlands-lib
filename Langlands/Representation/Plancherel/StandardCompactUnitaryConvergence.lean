import Langlands.Representation.Plancherel.CompactIntertwiningWeakRegularity
import Langlands.Representation.Plancherel.StandardIntertwiningScalarBounds
import Langlands.Representation.Twist.AdmissibilityProof

/-! # Absolute convergence at characters of equal modulus -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency.types false
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uG uI uV uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection) (A : SmoothRep.{0, uG, uV} ℂ M)
  {P' U' : Subgroup G}

/-- At parameters of equal character modulus, a fixed compact section has
scalar integrands of equal norm on the original radical quotient. -/
theorem norm_unramifiedCompactIntegrand_eq_of_character (χ η : unramifiedCharacters ν)
    (hχη : ∀ m : M, ‖(χ.val m : ℂ)‖ = ‖(η.val m : ℂ)‖)
    (f : CompactInductionPicture h K A) (g : G) (ℓ : Module.Dual ℂ A)
    (q : QuotientSpace (U := U) U') :
    ‖ℓ (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g χ q)‖ =
      ‖ℓ (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g η q)‖ := by
  induction q using Quotient.inductionOn with
  | h u =>
    obtain ⟨m, v, hv⟩ := unramifiedCompactExtension_eval_factor h hU hδ K hP hK hPK
      ν hν hr A f ((u : G) * g)
    calc
      _ = ‖ℓ ((χ.val m : ℂ) • v)‖ := congrArg (fun w : A => ‖ℓ w‖) (hv χ)
      _ = ‖ℓ ((η.val m : ℂ) • v)‖ := by
        rw [map_smul, map_smul, norm_smul, norm_smul, hχη m]
      _ = _ := (congrArg (fun w : A => ‖ℓ w‖) (hv η)).symm

variable (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [T2Space G] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [Measure.IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [Measure.IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G)) (hsq : SquaredModulusCompatibility h hU h' hU')

local notation "Aχ" => fun (χ : unramifiedCharacters ν) =>
  A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)

include hδ K hP hK hPK hν hr h' hU' μU' μI hqν hM hsq in
/-- Full weak convergence is invariant under changing the unitary phase of
the unramified inducing character. -/
theorem standardCompactFullDomain_of_character_norm_eq (hA : A.IsAdmissible)
    (χ η : unramifiedCharacters ν) (hχη : ∀ m : M, ‖(χ.val m : ℂ)‖ = ‖(η.val m : ℂ)‖)
    (hfull : domain h hU U' (Aχ χ) qν = ⊤) : domain h hU U' (Aχ η) qν = ⊤ := by
  have hAη : (Aχ η).IsAdmissible :=
    (isAdmissible_twist_iff η.val.toMonoidHom A.representation
      (unramifiedCharacter_isOpen_ker ν η)).mpr hA
  rw [← scalarDomain_eq_domain h hU U' (Aχ η) qν h' hU' μU' μI hqν hM hAη hsq]
  apply (scalarDomain_eq_top_iff_integrable_at_one h hU U' (Aχ η) qν).mpr
  intro f ℓ
  let e := unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr η A
  let f₀ := e f
  let ℓ₀ := smoothContragredientTwistEquiv η.val.toMonoidHom A.representation
    (unramifiedCharacter_isOpen_ker ν η) ℓ
  have hf : e.symm f₀ = f := e.symm_apply_apply f
  have hdom := unramifiedCompactIntegrand_scalar_integrable h hU hδ K hP hK hPK ν hν hr A
    U' qν χ hfull f₀ 1 ℓ₀
  apply hdom.mono (scalarIntegrand_aestronglyMeasurable h hU U' (Aχ η) qν 1 f ℓ)
  refine Filter.Eventually.of_forall fun q => ?_
  have hnorm := norm_unramifiedCompactIntegrand_eq_of_character h hU hδ K hP hK hPK
    ν hν hr A χ η hχη f₀ 1 ℓ₀.val q
  change _ = ‖ℓ.val (integrand h hU U' (Aχ η) 1 (e.symm f₀) q)‖ at hnorm
  rw [hf] at hnorm
  exact hnorm.ge

variable (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)

/-- The scalar tests of the actual compact integral are continuous along a
continuous family of full parameters of the same character modulus. -/
theorem continuous_standardCompactOperator_scalar_of_character_norm_eq
    {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]
    (c : X → unramifiedCharacters ν) (hc : Continuous c) (χ : unramifiedCharacters ν)
    (hmod : ∀ x m, ‖((c x).val m : ℂ)‖ = ‖(χ.val m : ℂ)‖)
    (hχ : domain h hU U' (Aχ χ) qν = ⊤)
    (hfull : ∀ x, domain h hU U' (Aχ (c x)) qν = ⊤)
    (f : CompactInductionPicture h K A) (k : K) (ℓ : SmoothDual A.representation) :
    Continuous (fun x => ℓ.val (eval _ _ (standardCompactOperator h hU hδ K hP hK hPK
      ν hν hr h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq (c x) A (hfull x) f) k)) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  apply continuousAt_standardCompactOperator_scalar_of_dominated h hU hδ K hP hK hPK ν hν hr A
    h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq c hc.continuousAt hfull f k ℓ
      (bound := fun q => ‖ℓ.val (unramifiedCompactIntegrand h hU hδ K hP hK hPK
        ν hν hr A U' f k χ q)‖)
  · exact Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun q =>
      (norm_unramifiedCompactIntegrand_eq_of_character h hU hδ K hP hK hPK ν hν hr A
        (c y) χ (hmod y) f k ℓ.val q).le
  · exact (unramifiedCompactIntegrand_scalar_integrable h hU hδ K hP hK hPK ν hν hr A
      U' qν χ hχ f k ℓ).norm

end Langlands.Plancherel
