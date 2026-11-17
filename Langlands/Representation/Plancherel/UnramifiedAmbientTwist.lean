import Langlands.Representation.Plancherel.StandardIntertwiningAmbientTwistLaws
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Ambient characters acting on actual unramified induction parameters -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (η : SmoothCharacter ℂ G) (hηU : U ≤ η.toMonoidHom.ker)
  (τ : unramifiedCharacters ν)
  (hτ : ∀ m : M, η.toMonoidHom (m : G) = τ.val m)
  (A : SmoothRep.{0, uG, uV} ℂ M) (z : unramifiedCharacters ν)

set_option hygiene false in
local notation "Az" => A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)

set_option hygiene false in
local notation "Aτz" =>
  A.twist (τ * z).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν (τ * z))

set_option hygiene false in
local notation "Azη" =>
  (Az).twist (subgroupSmoothCharacter η M).toMonoidHom
    (subgroupSmoothCharacter η M).isOpen_ker

include hτ in
/-- The restricted ambient twist of a variable Levi twist is its translated
unramified parameter, with the identity map on the coefficient carrier. -/
def ambientParameterCoefficientEquiv : (Azη).representation.Equiv (Aτz).representation :=
  equivOfRepresentationEq (by
    ext m v
    change (η.toMonoidHom (m : G) : ℂ) •
        ((z.val m : ℂ) • A.representation m v) =
      ((τ.val m * z.val m : ℂˣ) : ℂ) • A.representation m v
    rw [hτ]
    simp only [Units.val_mul, smul_smul])

omit [LocallyCompactSpace G] in
@[simp]
theorem ambientParameterCoefficientEquiv_apply (v : A) :
    ambientParameterCoefficientEquiv ν η τ hτ A z v = v := rfl

/-- The actual induced equivalence attached to a coefficient equivalence in
Levi-inflated normalization. -/
private def leviInducedEquiv {B C : SmoothRep.{0, uG, uV} ℂ M}
    (e : B.representation.Equiv C.representation) :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj B).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj C).representation :=
  smoothInducedEquiv P (Representation.Equiv.mk e.toLinearEquiv
    (fun p => (twistEquiv
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer) e).isIntertwining'
        (h.projection p)))

/-- Ambient character multiplication realizes translation of the actual
unramified parameter of the induced representation. -/
def ambientParameterInductionEquiv :
    (Langlands.twist η.toMonoidHom
      (UnramifiedLeviInduction h hU ν z A).representation).Equiv
      (UnramifiedLeviInduction h hU ν (τ * z) A).representation :=
  (leviInductionCharacterTwistEquiv h hU η hηU Az).trans
    (leviInducedEquiv h hU (ambientParameterCoefficientEquiv ν η τ hτ A z))

@[simp]
theorem ambientParameterInductionEquiv_eval
    (f : UnramifiedLeviInduction h hU ν z A) (g : G) :
    eval P (leviInflatedInducingRepresentation h hU Aτz)
        (ambientParameterInductionEquiv h hU ν η hηU τ hτ A z f) g =
      (η.toMonoidHom g : ℂ) •
        eval P (leviInflatedInducingRepresentation h hU Az) f g := rfl

variable (U' : Subgroup G) (hηU' : U' ≤ η.toMonoidHom.ker)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

include hηU hηU' hτ in
/-- Translation by a restricted ambient character preserves the full actual
convergence domain, including representability in the original carrier. -/
theorem domain_eq_top_ambientParameter_iff :
    domain h hU U' Aτz qν = ⊤ ↔ domain h hU U' Az qν = ⊤ :=
  (domain_eq_top_iff_equiv h hU U' qν
    (ambientParameterCoefficientEquiv ν η τ hτ A z)).symm.trans
      (domain_eq_top_characterTwist_iff h hU η hηU Az U' hηU' qν)

section Compact

variable (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hηK : K.toSubgroup ≤ η.toMonoidHom.ker)

include hηK

/-- An ambient character trivial on the chosen compact subgroup induces the
identity on the fixed compact picture at corresponding parameters. -/
theorem ambientParameterInductionEquiv_compact
    (f : UnramifiedLeviInduction h hU ν z A) :
    unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr (τ * z) A
        (ambientParameterInductionEquiv h hU ν η hηU τ hτ A z f) =
      unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr z A f := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change eval P (leviInflatedInducingRepresentation h hU Aτz)
      (ambientParameterInductionEquiv h hU ν η hηU τ hτ A z f) (k : G) =
    eval P (leviInflatedInducingRepresentation h hU Az) f (k : G)
  rw [ambientParameterInductionEquiv_eval]
  have hk : η.toMonoidHom (k : G) = 1 := hηK k.property
  rw [hk, Units.val_one, one_smul]

/-- The inverse compact extension is ambient character multiplication of the
original extension. -/
theorem ambientParameterInductionEquiv_compact_symm
    (f : CompactInductionPicture h K A) :
    (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr
      (τ * z) A).symm f =
      ambientParameterInductionEquiv h hU ν η hηU τ hτ A z
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr z A).symm f) := by
  apply (unramifiedLeviInductionCompactEquiv
    h hU hδ K hP hK hPK ν hν hr (τ * z) A).injective
  rw [LinearEquiv.apply_symm_apply, ambientParameterInductionEquiv_compact,
    LinearEquiv.apply_symm_apply]
  exact hηK

end Compact

section Target

variable {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The actual full-source standard integral at translated parameters is
conjugate by ambient character multiplication, in the original Haar scale. -/
theorem fullSourceIntertwiner_ambientParameter
    (hfull : domain h hU U' Az qν = ⊤)
    (hfullτ : domain h hU U' Aτz qν = ⊤)
    (f : UnramifiedLeviInduction h hU ν z A) :
    fullSourceIntertwiner h hU h' hU' Aτz qν μU' μI hqν hM hsq hfullτ
        (ambientParameterInductionEquiv h hU ν η hηU τ hτ A z f) =
      ambientParameterInductionEquiv h' hU' ν η hηU' τ hτ A z
        (fullSourceIntertwiner h hU h' hU' Az qν μU' μI hqν hM hsq hfull f) := by
  let hfullη := (domain_eq_top_characterTwist_iff h hU η hηU Az U' hηU' qν).mpr hfull
  have hn := congrArg
    (fun T => T (leviInductionCharacterTwistEquiv h hU η hηU Az f))
    (fullSourceIntertwiner_natural h hU h' hU' qν μU' μI hqν hM hsq
      hfullη hfullτ (ambientParameterCoefficientEquiv ν η τ hτ A z).toIntertwiningMap)
  have hc := fullSourceIntertwiner_characterTwist h hU η hηU Az U' hηU' qν hM
    h' hU' μU' μI hqν hsq hfull f
  exact hn.trans (congrArg
    (inducedMap h' hU' (ambientParameterCoefficientEquiv ν η τ hτ A z).toIntertwiningMap)
    hc)

variable (hδ : IsUnimodularModulus U hU) (hδ' : IsUnimodularModulus U' hU')
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
  (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection) (hr' : Continuous h'.projection)
  (hηK : K.toSubgroup ≤ η.toMonoidHom.ker)

include hηU hηU' hτ hηK in
/-- On the fixed compact picture, translation by a restricted ambient
character leaves the actual standard integral unchanged. -/
theorem standardCompactOperator_ambientParameter
    (hfull : domain h hU U' Az qν = ⊤)
    (hfullτ : domain h hU U' Aτz qν = ⊤) :
    standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq (τ * z) A hfullτ =
      standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq z A hfull := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change eval P' (leviInflatedInducingRepresentation h' hU' Aτz)
      (fullSourceIntertwiner h hU h' hU' Aτz qν μU' μI hqν hM hsq hfullτ
        ((unramifiedLeviInductionCompactEquiv
          h hU hδ K hP hK hPK ν hν hr (τ * z) A).symm f)) (k : G) =
    eval P' (leviInflatedInducingRepresentation h' hU' Az)
      (fullSourceIntertwiner h hU h' hU' Az qν μU' μI hqν hM hsq hfull
        ((unramifiedLeviInductionCompactEquiv
          h hU hδ K hP hK hPK ν hν hr z A).symm f)) (k : G)
  rw [ambientParameterInductionEquiv_compact_symm
    h hU ν η hηU τ hτ A z hδ K hP hK hPK hν hr hηK]
  rw [fullSourceIntertwiner_ambientParameter h hU ν η hηU τ hτ A z U' hηU' qν
    h' hU' μU' μI hqν hM hsq]
  rw [ambientParameterInductionEquiv_eval]
  have hk : η.toMonoidHom (k : G) = 1 := hηK k.property
  rw [hk, Units.val_one, one_smul]

end Target

end Langlands.Plancherel
