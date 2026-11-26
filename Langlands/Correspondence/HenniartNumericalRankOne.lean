import Langlands.Correspondence.HenniartRefinedStrataProof
import Langlands.Correspondence.HenniartWeilArtinConductorExistenceProof
import Langlands.Correspondence.HenniartWeilRankOneCountProof
import Langlands.Representation.Conductor.RankOneMultiplicativeConductor

/-!
# The numerical correspondence in rank one

The rank-one reciprocity bijection preserves conductors and unramified twists.
The rank-one refined orbit counts therefore agree, which implies that every
rank-one numerical injection is surjective.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Henniart

open Correspondence Numerical

universe uK uW uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local notation "T" => K.canonicalTopologicalData

private local instance : TopologicalSpace K.Carrier := (T).topology
private local instance : ValuativeRel K.Carrier := (T).valuativeRel
private local instance : IsNonarchimedeanLocalField K.Carrier := (T).localField

/-- The newvector conductor of the scalar `GL₁` class is the multiplicative
conductor of its field character. -/
theorem rankOneSupercuspidal_conductor (χ : QuasiCharacter K) :
    conductor K (k := 0) (rankOneSupercuspidalClass.{uK, uV} K χ) =
      ((T).multiplicativeConductor χ : WithTop ℕ) := by
  change Conductor.firstFixedLevel (rankOneSupercuspidalObject.{uK, uV} K χ).obj.representation =
    _
  exact Conductor.firstFixedLevel_eq_multiplicativeConductor χ
    (FiniteRepresentation.characterLineEquiv (determinantQuasiCharacter K 1 χ))

private theorem rankOneReciprocityEquiv_unramifiedTwist
    (e : ReciprocityCandidate K) (he : IsGeometricReciprocity K e)
    (z : ℂˣ) (σ : IrreducibleWeilClass.{uK, uW} K 1) :
    rankOneReciprocityEquiv.{uK, uW, uV} K e (weilUnramifiedTwist K 0 z σ) =
      supercuspidalUnramifiedTwist K 0 z (rankOneReciprocityEquiv K e σ) := by
  have hχ : LocalFactor.RankOne.weilCharacter K e ((T).unramifiedCharacterContinuous z) =
      Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z := by
    apply ContinuousMonoidHom.ext
    intro w
    change z ^ (T).ord (reciprocityHom K e w : K.Carrier) = z ^ Weil.Local.localDegreeInt K w
    rw [ord_reciprocityHom K he]
  have htw := rankOneReciprocityEquiv_twist.{uK, uW, uV} K e σ
    ((T).unramifiedCharacterContinuous z)
  rw [hχ] at htw
  exact (isSupercuspidalCharacterTwist_iff_eq_twist K (n := 1) ((T).unramifiedCharacterContinuous z)
    ((T).isOpen_ker_determinantUnramifiedCharacter 1 z) _ _).mp htw

/-- Geometric reciprocity is a bijection in rank one with the two numerical
compatibilities. -/
def rankOneNumericalEquiv (e : ReciprocityCandidate K) (he : IsGeometricReciprocity K e) :
    {f : IrreducibleWeilClass.{uK, uW} K 1 ≃ SupercuspidalAutomorphicClass.{uK, uV} K 1 //
      IsNumericalInjection K (k := 0) (f : _ → _)} := by
  refine ⟨rankOneReciprocityEquiv K e, (rankOneReciprocityEquiv K e).injective, ?_,
    rankOneReciprocityEquiv_unramifiedTwist K e he⟩
  intro σ a ha
  obtain ⟨χ, rfl⟩ := rankOneWeilCharacterClass_surjective K e σ
  rw [rankOneReciprocityEquiv_character, rankOneSupercuspidal_conductor]
  exact congrArg (fun n : ℕ => (n : WithTop ℕ))
    ((rankOne_hasArtinConductor_iff K e he χ a).mp ha).symm

/-- The two refined orbit strata have equal finite counts in rank one at
every slope bound. -/
theorem rankOneCountsAgreeUpToSlope (x : ℝ) :
    CountsAgreeUpToSlope.{uK, uW, uV} K x 1 := by
  obtain ⟨e, he, -⟩ := LocalClassField.weilReciprocityTheorems.{uK}.1 p K T
  let f := rankOneNumericalEquiv.{uK, uW, uV} K e he
  apply ((refinedStrata.{uK, uW, uV}).2 p K x 1).2
  · exact fun k _ σ => weilArtinConductorExistence p K k σ
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact ⟨f.val, f.property, fun π _ _ _ => f.val.surjective π⟩

/-- The rank-one case of numerical surjectivity for any numerical injection. -/
theorem rankOneNumericalInjection_surjective
    (φ : IrreducibleWeilClass.{uK, uW} K 1 → SupercuspidalAutomorphicClass.{uK, uV} K 1)
    (hφ : IsNumericalInjection K (k := 0) φ) :
    Function.Surjective φ := by
  intro π
  obtain ⟨χ, rfl⟩ := rankOneSupercuspidalClass_surjective K π
  let a := (T).multiplicativeConductor χ
  let s := a - 1
  have hs : HasSupercuspidalSwan K (k := 0) (rankOneSupercuspidalClass K χ) s :=
    ⟨a, rankOneSupercuspidal_conductor K χ, rfl⟩
  exact ((refinedStrata.{uK, uW, uV}).2 p K s 1).1
    (rankOneCountsAgreeUpToSlope K s) 0 (by decide) φ hφ _ s hs (by simp)

end Langlands.Henniart
