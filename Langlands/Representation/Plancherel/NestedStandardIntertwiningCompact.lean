import Langlands.Representation.Plancherel.NestedStandardIntertwiningStages
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.UnramifiedCharacterTransport
import Mathlib.Algebra.Module.Projective

/-! # A fixed compact-picture restriction to an intermediate Levi -/

noncomputable section

open Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

universe u uV uI

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L N : Subgroup G} [LocallyCompactSpace L]
  (h : IsSemidirectDecomposition P M U) (hQ : IsSemidirectDecomposition Q L N)
  (hLc : IsClosed (L : Set G)) (hML : M ≤ L)
  (hL : IsSemidirectDecomposition (P.subgroupOf L) (M.subgroupOf L) (U.subgroupOf L))
  (hU : IsClosed (U : Set G)) (hN : IsClosed (N : Set G))
  (hPQ : P ≤ Q) (hNU : N ≤ U) (hπ : Continuous hQ.projection)
  (hδU : IsUnimodularModulus U hU) (hδN : IsUnimodularModulus N hN)
  (hhalf : NestedInduction.HalfCharacterProduct h hQ hLc hL hU hN)
  (A : SmoothRep.{0, u, uV} ℂ M)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hproj : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))

set_option hygiene false in
local notation "hUi" => hU.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "hPi" => hP.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "Ai" => SmoothRep.pullback (subgroupOfContinuousEquiv hML) A
set_option hygiene false in
local notation "Ki" => K.comap L.subtype continuous_subtype_val
set_option hygiene false in
local notation "eM" => subgroupOfContinuousEquiv hML
set_option hygiene false in
local notation "νi" => (fun i => (ν i).comp (eM).toMonoidHom)
set_option hygiene false in
local notation "restrictParam" => unramifiedCharactersHomeomorph (eM).symm ν

variable (hδUi : IsUnimodularModulus (U.subgroupOf L) hUi)
  (hPiKi : ∀ l : L, ∃ p : P.subgroupOf L, ∃ k : Ki, l = (p : L) * (k : L))
  (hproji : Continuous hL.projection)

set_option hygiene false in
local notation "χA" => A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)

set_option hygiene false in
local notation "srcEquiv" =>
  unramifiedLeviInductionCompactEquiv h hU hδU K hP hK hPK ν hν hproj χ A

set_option hygiene false in
local notation "innerEquiv" =>
  unramifiedLeviInductionCompactEquiv hL hUi hδUi Ki hPi
    (hLc.isClosedEmbedding_subtypeVal.isCompact_preimage hK) hPiKi
    νi (fun i => (hν i).comp (eM).continuous) hproji (restrictParam χ) Ai

set_option hygiene false in
local notation "stageMap" =>
  nestedStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf χA hδUi 1

/-- Conjugate the actual stages restriction by the ambient and inner
compact-picture equivalences. The inner compact subgroup is the actual
intersection with the intermediate Levi. -/
def compactStagesRestriction (χ : unramifiedCharacters ν) :
    CompactInductionPicture h K A →ₗ[ℂ] CompactInductionPicture hL Ki Ai :=
  (innerEquiv).toLinearMap.comp ((stageMap).comp (srcEquiv).symm.toLinearMap)

/-- At an inner compact point the restriction value uses only the input
compact value and the fixed outer half-character. -/
theorem compactStagesRestriction_eval
    (χ : unramifiedCharacters ν) (f : CompactInductionPicture h K A) (k : Ki) :
    eval _ _
      (compactStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
        K hK hP hPK hproj ν hν hδUi hPiKi hproji χ f) k =
      (↑(HaarModulus.closedHalfCharacter N hN L hQ.levi_le_normalizer (k : L))⁻¹ : ℂ) •
        eval _ _ f ⟨((k : L) : G), k.property⟩ := by
  let F := (srcEquiv).symm f
  have he := nestedStagesRestriction_formula h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf
    χA hδUi F 1 (k : L)
  have ha := unramifiedLeviInductionCompactEquiv_eval h hU hδU K hP hK hPK ν hν hproj χ A
    F ⟨((k : L) : G), k.property⟩
  have ha' : eval P (leviInflatedInducingRepresentation h hU χA) F ((k : L) : G) =
      eval _ _ f ⟨((k : L) : G), k.property⟩ := by
    change eval _ _ (srcEquiv ((srcEquiv).symm f)) ⟨((k : L) : G), k.property⟩ =
      eval P (leviInflatedInducingRepresentation h hU χA) F ((k : L) : G) at ha
    rw [LinearEquiv.apply_symm_apply] at ha
    exact ha.symm
  change eval (P.subgroupOf L) (leviInflatedInducingRepresentation hL hUi
    (SmoothRep.pullback eM χA)) (stageMap F) (k : L) = _
  simpa only [mul_one, ha'] using he

/-- The compact-picture restriction is surjective at every parameter. -/
theorem compactStagesRestriction_surjective (χ : unramifiedCharacters ν) :
    Function.Surjective
      (compactStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
        K hK hP hPK hproj ν hν hδUi hPiKi hproji χ) :=
  (innerEquiv).surjective.comp
    ((nestedStagesRestriction_surjective h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf
      χA hδUi).comp (srcEquiv).symm.surjective)

/-- The compact restriction is a fixed linear map on the entire unramified
parameter space. -/
theorem compactStagesRestriction_independent (χ ψ : unramifiedCharacters ν) :
    compactStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
        K hK hP hPK hproj ν hν hδUi hPiKi hproji χ =
      compactStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
        K hK hP hPK hproj ν hν hδUi hPiKi hproji ψ := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact (compactStagesRestriction_eval h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
    K hK hP hPK hproj ν hν hδUi hPiKi hproji χ f k).trans
    (compactStagesRestriction_eval h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
      K hK hP hPK hproj ν hν hδUi hPiKi hproji ψ f k).symm

/-- A single linear section of the compact restriction works for all
unramified parameters. -/
theorem exists_compactStagesRestriction_rightInverse :
    ∃ S : CompactInductionPicture hL Ki Ai →ₗ[ℂ] CompactInductionPicture h K A,
      ∀ χ : unramifiedCharacters ν,
        (compactStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
          K hK hP hPK hproj ν hν hδUi hPiKi hproji χ).comp S = LinearMap.id := by
  let R := compactStagesRestriction h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
    K hK hP hPK hproj ν hν hδUi hPiKi hproji 1
  have hs : Function.Surjective R := compactStagesRestriction_surjective
    h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
      K hK hP hPK hproj ν hν hδUi hPiKi hproji 1
  obtain ⟨S, hS⟩ := R.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  refine ⟨S, fun χ => ?_⟩
  have he := compactStagesRestriction_independent
    h hQ hLc hML hL hU hN hPQ hNU hπ hδU hδN hhalf A
      K hK hP hPK hproj ν hν hδUi hPiKi hproji χ 1
  exact (congrArg (fun r => r.comp S) he).trans hS

end Langlands.Plancherel.StandardIntertwining
