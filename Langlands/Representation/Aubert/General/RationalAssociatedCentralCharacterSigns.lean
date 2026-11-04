import Langlands.Representation.Aubert.General.RationalAssociatedCocharacterTransport
import Mathlib.RepresentationTheory.Intertwining

/-! # Scalar characters under actual associated-Levi conjugation -/

noncomputable section

open scoped NNReal

namespace Langlands.Aubert.General

universe uH uK uV uW

/-- Nonzero representations related by a group pullback and an actual
representation equivalence have corresponding full-center scalar characters. -/
theorem scalarCharacter_eq_of_pullback_equiv
    {H : Type uH} [Group H] {K : Type uK} [Group K]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (e : H ≃* K) (τ : Representation ℂ H V) (ρ : Representation ℂ K W)
    (E : τ.Equiv (ρ.comp e.toMonoidHom))
    (χH : Subgroup.center H →* ℂˣ) (χK : Subgroup.center K →* ℂˣ)
    (hH : ∀ (z : Subgroup.center H) (v : V), τ (z : H) v = (χH z : ℂ) • v)
    (hK : ∀ (z : Subgroup.center K) (w : W), ρ (z : K) w = (χK z : ℂ) • w)
    (z : Subgroup.center H) :
    χH z = χK (Subgroup.centerCongr e z) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hEv : E.toLinearEquiv v ≠ 0 := by
    intro heq
    exact hv (E.toLinearEquiv.injective
      (heq.trans E.toLinearEquiv.map_zero.symm))
  apply Units.ext
  apply smul_left_injective ℂ hEv
  calc
    (χH z : ℂ) • E.toLinearEquiv v = E.toLinearEquiv (τ (z : H) v) := by
      rw [hH, map_smul]
    _ = (ρ.comp e.toMonoidHom) (z : H) (E.toLinearEquiv v) := by
      exact Representation.IntertwiningMap.isIntertwining τ
        (ρ.comp e.toMonoidHom) E.toIntertwiningMap (z : H) v
    _ = (χK (Subgroup.centerCongr e z) : ℂ) • E.toLinearEquiv v := by
      exact hK (Subgroup.centerCongr e z) (E.toLinearEquiv v)

end Langlands.Aubert.General

namespace Langlands.Plancherel

/-- The residue-normalized norm logarithm reverses sign under inversion. -/
theorem normLog_inv (q : ℝ) (x : ℝ≥0ˣ) : normLog q x⁻¹ = -normLog q x := by
  have h := normLog_mul q x x⁻¹
  rw [mul_inv_cancel, normLog_one] at h
  linarith

end Langlands.Plancherel


open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v w

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The common-uniformizer point of a specified standard cocharacter, as an
element of the actual full abstract Levi center. -/
def standardCocharacterUniformizerCenter
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Finset (SimpleRoot i ν))
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν J) ζ}) :
    Subgroup.center (levi i ν J) :=
  leviCentralTorusPointToCenter i ν J
    (leviCentralUniformizerSection i ν hfinite J ⟨ζ.val, ζ.property⟩
      (.ofAdd ⟨ζ.val, mem_cocharacterAnnihilator.mpr ζ.property.2.1⟩))

@[simp] theorem standardCocharacterUniformizerCenter_val
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Finset (SimpleRoot i ν))
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν J) ζ}) :
    ((standardCocharacterUniformizerCenter i ν hfinite J ζ : levi i ν J) :
      rationalPoints G) = uniformizerPowers i (.ofAdd ζ.val) := rfl

local instance associatedCharacterAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [Mono i.hom.hom.left] [IsTopologicalGroup (rationalPoints G)]
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)

/-- Literal conjugation by the chosen longest lift from the associated Levi
center to the original Levi center. -/
def associatedLeviCenterConjugationEquiv
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    Subgroup.center (levi i ν (associatedSubset cs J)) ≃*
      Subgroup.center (levi i ν J) :=
  Subgroup.centerCongr
    (associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc J n hn).symm.toMulEquiv

/-- The full-center map sends the actual associated-opposite uniformizer
point to the inverse of the original point, retaining the specified lift. -/
theorem associatedLeviCenterConjugationEquiv_standardUniformizer
    (hRoots : HasRelativeRootSystem i)
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν J) ζ}) :
    associatedLeviCenterConjugationEquiv i ν hG hi hν hConj hN hZ cs
        hLength hSimple hMin hAssoc J n hn
      (standardCocharacterUniformizerCenter i ν
        (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) _
        (associatedOppositeStandardCocharacter i ν hN hZ cs hLength hSimple hMin
          hAssoc hi.isSplitSubtorus.1 hRoots hν J n hn ζ)) =
      (standardCocharacterUniformizerCenter i ν
        (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) J ζ)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  change (n : rationalPoints G) *
      uniformizerPowers i (.ofAdd
        (associatedOppositeCocharacter i ((normalizerEquiv i hN).symm n) ζ.val)) *
      (n : rationalPoints G)⁻¹ = (uniformizerPowers i (.ofAdd ζ.val))⁻¹
  exact uniformizerPowers_associatedOpposite_conj i ((normalizerEquiv i hN).symm n) ζ.val

/-- Pull back a full abstract center character by the specified actual
longest conjugation. -/
def associatedLeviCentralCharacter
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (χ : Subgroup.center (levi i ν J) →* ℂˣ) :
    Subgroup.center (levi i ν (associatedSubset cs J)) →* ℂˣ :=
  χ.comp (associatedLeviCenterConjugationEquiv i ν hG hi hν hConj hN hZ cs
    hLength hSimple hMin hAssoc J n hn).toMonoidHom

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Actual representation equivalence identifies the associated scalar
character with this pullback, without any unitarity hypothesis. -/
theorem scalarCharacter_eq_associatedLeviCentralCharacter
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (levi i ν (associatedSubset cs J)) V)
    (ρ : Representation ℂ (levi i ν J) W)
    (E : τ.Equiv (ρ.comp (associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc J n hn).symm.toMonoidHom))
    (χ₂ : Subgroup.center (levi i ν (associatedSubset cs J)) →* ℂˣ)
    (χ₁ : Subgroup.center (levi i ν J) →* ℂˣ)
    (h₂ : ∀ (z : Subgroup.center (levi i ν (associatedSubset cs J))) (v : V),
      τ (z : levi i ν (associatedSubset cs J)) v = (χ₂ z : ℂ) • v)
    (h₁ : ∀ (z : Subgroup.center (levi i ν J)) (w : W),
      ρ (z : levi i ν J) w = (χ₁ z : ℂ) • w) :
    χ₂ = associatedLeviCentralCharacter i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc J n hn χ₁ := by
  apply MonoidHom.ext
  intro z
  exact scalarCharacter_eq_of_pullback_equiv
    (associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc J n hn).symm.toMulEquiv τ ρ E χ₂ χ₁ h₂ h₁ z

/-- The associated character at the actual associated-opposite uniformizer
point is the inverse original character value. -/
theorem associatedLeviCentralCharacter_standardUniformizer
    (hRoots : HasRelativeRootSystem i)
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν J) ζ})
    (χ : Subgroup.center (levi i ν J) →* ℂˣ) :
    associatedLeviCentralCharacter i ν hG hi hν hConj hN hZ cs
        hLength hSimple hMin hAssoc J n hn χ
      (standardCocharacterUniformizerCenter i ν
        (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) _
        (associatedOppositeStandardCocharacter i ν hN hZ cs hLength hSimple hMin
          hAssoc hi.isSplitSubtorus.1 hRoots hν J n hn ζ)) =
      (χ (standardCocharacterUniformizerCenter i ν
        (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) J ζ))⁻¹ := by
  change χ (associatedLeviCenterConjugationEquiv i ν hG hi hν hConj hN hZ cs
    hLength hSimple hMin hAssoc J n hn _) = _
  rw [associatedLeviCenterConjugationEquiv_standardUniformizer, map_inv]

/-- Logarithmic moduli on the two actual standard cocharacter points are
opposite, using the common uniformizer and its actual longest lift. -/
theorem associatedLeviCentralCharacter_latticeLog
    (hRoots : HasRelativeRootSystem i)
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν J) ζ})
    (χ : Subgroup.center (levi i ν J) →* ℂˣ) :
    let hfinite := hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν
    let ξ := associatedOppositeStandardCocharacter i ν hN hZ cs hLength hSimple hMin
      hAssoc hi.isSplitSubtorus.1 hRoots hν J n hn ζ
    leviCentralLatticeCharacterLog i ν hfinite _ ⟨ξ.val, ξ.property⟩
        (associatedLeviCentralCharacter i ν hG hi hν hConj hN hZ cs
          hLength hSimple hMin hAssoc J n hn χ)
        ⟨ξ.val, mem_cocharacterAnnihilator.mpr ξ.property.2.1⟩ =
      -leviCentralLatticeCharacterLog i ν hfinite J ⟨ζ.val, ζ.property⟩ χ
        ⟨ζ.val, mem_cocharacterAnnihilator.mpr ζ.property.2.1⟩ := by
  have hc := associatedLeviCentralCharacter_standardUniformizer i ν hG hi hν hConj
    hN hZ cs hLength hSimple hMin hAssoc hRoots J n hn ζ χ
  have hl := congrArg (fun a : ℂˣ =>
    Plancherel.normLog (LocalField.residueCardinality k)
      (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom a)) hc
  change Plancherel.normLog (LocalField.residueCardinality k) _ =
    -Plancherel.normLog (LocalField.residueCardinality k) _
  simpa only [standardCocharacterUniformizerCenter, PositiveCharacter.normCharacter,
    MonoidHom.comp_apply, map_inv, Plancherel.normLog_inv] using hl

end Langlands.Aubert.General.RationalPointFamily
