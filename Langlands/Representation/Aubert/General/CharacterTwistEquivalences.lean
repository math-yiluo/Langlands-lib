import Langlands.Representation.Aubert.GeneralCorollaryTargets
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Jacquet.CharacterTwistEquiv
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Smooth.LengthTwoEndpoints

/-! # Scalar twists of the actual general normalized parabolic functors -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Aubert.General

universe uG uV uI

section Projection

variable {G : Type uG} [Group G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U)

/-- A character killing the radical factors through the actual Levi projection. -/
theorem character_eq_projection {A : Type*} [Group A] (χ : G →* A)
    (hχU : U ≤ χ.ker) (p : P) :
    χ (p : G) = χ ((h.projection p : M) : G) := by
  have hk : χ (((h.projection p : M) : G)⁻¹ * (p : G)) = 1 :=
    hχU (h.projection_inv_mul_mem p)
  rw [map_mul, map_inv] at hk
  exact (inv_mul_eq_one.mp hk).symm

end Projection

section Topology

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Restriction along the actual subgroup inclusion, with its inherited topology. -/
def subgroupSmoothCharacter (χ : Induction.SmoothCharacter ℂ G) (H : Subgroup G) :
    Induction.SmoothCharacter ℂ H where
  toMonoidHom := χ.toMonoidHom.comp H.subtype
  isOpen_ker := χ.isOpen_ker.preimage continuous_subtype_val

end Topology

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  (χ : Induction.SmoothCharacter ℂ G) (hχU : U ≤ χ.toMonoidHom.ker)

include hχU

/-- The scalar twist commutes with inflation and the positive half modulus. -/
theorem inducingRepresentation_characterTwist (A : SmoothRep.{0, uG, uV} ℂ M) :
    Langlands.twist (χ.toMonoidHom.comp P.subtype) (inducingRepresentation h hU A) =
      inducingRepresentation h hU
        (A.twist (subgroupSmoothCharacter χ M).toMonoidHom
          (subgroupSmoothCharacter χ M).isOpen_ker) := by
  ext p v
  change (χ.toMonoidHom (p : G) : ℂ) •
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
        A.representation (h.projection p) v) =
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
      ((χ.toMonoidHom ((h.projection p : M) : G) : ℂ) •
        A.representation (h.projection p) v)
  rw [character_eq_projection h χ.toMonoidHom hχU p]
  exact smul_comm _ _ _

/-- Character multiplication on actual normalized induced functions. -/
def normalizedInductionCharacterTwistEquiv (A : SmoothRep.{0, uG, uV} ℂ M) :
    (Langlands.twist χ.toMonoidHom
      ((normalizedInductionFunctor h hU).obj A).representation).Equiv
      ((normalizedInductionFunctor h hU).obj
        (A.twist (subgroupSmoothCharacter χ M).toMonoidHom
          (subgroupSmoothCharacter χ M).isOpen_ker)).representation :=
  (Induction.smoothInductionTwistEquiv P χ (inducingRepresentation h hU A)).trans
    (Induction.smoothInducedEquiv P (equivOfRepresentationEq
      (inducingRepresentation_characterTwist h hU χ hχU A)))

@[simp]
theorem normalizedInductionCharacterTwistEquiv_eval
    (A : SmoothRep.{0, uG, uV} ℂ M) (f : (normalizedInductionFunctor h hU).obj A)
    (x : G) :
    Induction.eval P _ (normalizedInductionCharacterTwistEquiv h hU χ hχU A f) x =
      (χ.toMonoidHom x : ℂ) • Induction.eval P (inducingRepresentation h hU A) f x := rfl

@[simp]
theorem normalizedInductionCharacterTwistEquiv_symm_eval
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj
      (A.twist (subgroupSmoothCharacter χ M).toMonoidHom
        (subgroupSmoothCharacter χ M).isOpen_ker)) (x : G) :
    Induction.eval P (inducingRepresentation h hU A)
        ((normalizedInductionCharacterTwistEquiv h hU χ hχU A).symm f) x =
      ((χ.toMonoidHom x)⁻¹ : ℂˣ) • Induction.eval P _ f x := rfl

/-- The character-multiplication comparison is natural on the full smooth category. -/
def normalizedInductionCharacterTwistIso :
    normalizedInductionFunctor.{uG, uV} h hU ⋙
        SmoothRep.twistFunctor χ.toMonoidHom χ.isOpen_ker ≅
      SmoothRep.twistFunctor (subgroupSmoothCharacter χ M).toMonoidHom
          (subgroupSmoothCharacter χ M).isOpen_ker ⋙
        normalizedInductionFunctor h hU :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (normalizedInductionCharacterTwistEquiv h hU χ hχU A))
    (fun {A B} f => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      apply Subtype.ext
      funext x
      change (χ.toMonoidHom x : ℂ) •
          SmoothRep.hom f (Induction.eval P (inducingRepresentation h hU A) z x) =
        SmoothRep.hom f ((χ.toMonoidHom x : ℂ) •
          Induction.eval P (inducingRepresentation h hU A) z x)
      exact (map_smul (SmoothRep.hom f) _ _).symm)

/-- A radical-trivial twist of the inducing object preserves reducibility. -/
theorem normalizedInduction_isIrreducible_characterTwist_iff
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj
      (A.twist (subgroupSmoothCharacter χ M).toMonoidHom
        (subgroupSmoothCharacter χ M).isOpen_ker)).IsIrreducible ↔
      ((normalizedInductionFunctor h hU).obj A).IsIrreducible := by
  let E := (normalizedInductionCharacterTwistIso h hU χ hχU).app A
  constructor
  · intro hA
    exact (SmoothRep.isIrreducible_twist_iff χ.toMonoidHom χ.isOpen_ker _).mp
      (SmoothRep.isIrreducible_of_iso E.symm hA)
  · intro hA
    exact SmoothRep.isIrreducible_of_iso E
      ((SmoothRep.isIrreducible_twist_iff χ.toMonoidHom χ.isOpen_ker _).mpr hA)

end Induction

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  (U M : Subgroup G) (hU : IsClosed (U : Set G))
  (hMU : M ≤ Subgroup.normalizer (U : Set G))
  (χ : Induction.SmoothCharacter ℂ G) (hχU : U ≤ χ.toMonoidHom.ker)

include hχU

/-- The actual normalized quotient comparison sends the class of v to the class of v. -/
def normalizedJacquetCharacterTwistEquiv (A : SmoothRep.{0, uG, uV} ℂ G) :
    ((normalizedJacquetFunctor U M hU hMU).obj
      (A.twist χ.toMonoidHom χ.isOpen_ker)).representation.Equiv
      (Langlands.twist (subgroupSmoothCharacter χ M).toMonoidHom
        ((normalizedJacquetFunctor U M hU hMU).obj A).representation) :=
  (twistEquiv (HaarModulus.closedInverseHalfCharacter U hU M hMU)
    (Jacquet.Localization.trivialEquiv (Langlands.twist χ.toMonoidHom A.representation)
      U M hMU)).trans
    ((Jacquet.twistActionTwistEquiv A.representation U M hMU χ.toMonoidHom hχU
      (HaarModulus.closedInverseHalfCharacter U hU M hMU)).trans
        (twistEquiv (subgroupSmoothCharacter χ M).toMonoidHom
          (twistEquiv (HaarModulus.closedInverseHalfCharacter U hU M hMU)
            (Jacquet.Localization.trivialEquiv A.representation U M hMU).symm)))

@[simp]
theorem normalizedJacquetCharacterTwistEquiv_mk
    (A : SmoothRep.{0, uG, uV} ℂ G) (v : A) :
    normalizedJacquetCharacterTwistEquiv U M hU hMU χ hχU A
        (Jacquet.Localization.mk (Langlands.twist χ.toMonoidHom A.representation) U 1 v) =
      Jacquet.Localization.mk A.representation U 1 v := rfl

@[simp]
theorem normalizedJacquetCharacterTwistEquiv_symm_mk
    (A : SmoothRep.{0, uG, uV} ℂ G) (v : A) :
    (normalizedJacquetCharacterTwistEquiv U M hU hMU χ hχU A).symm
        (Jacquet.Localization.mk A.representation U 1 v) =
      Jacquet.Localization.mk (Langlands.twist χ.toMonoidHom A.representation) U 1 v := rfl

/-- The actual quotient comparison is natural on the full smooth category. -/
def normalizedJacquetCharacterTwistIso :
    SmoothRep.twistFunctor.{0, uG, uV} χ.toMonoidHom χ.isOpen_ker ⋙
        normalizedJacquetFunctor U M hU hMU ≅
      normalizedJacquetFunctor U M hU hMU ⋙
        SmoothRep.twistFunctor (subgroupSmoothCharacter χ M).toMonoidHom
          (subgroupSmoothCharacter χ M).isOpen_ker :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (normalizedJacquetCharacterTwistEquiv U M hU hMU χ hχU A))
    (fun {A B} f => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
        (Langlands.twist χ.toMonoidHom A.representation) U 1 z
      rfl)

/-- Vanishing of the actual normalized Jacquet module is invariant under the twist. -/
theorem normalizedJacquet_isZero_characterTwist_iff
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    IsZero ((normalizedJacquetFunctor U M hU hMU).obj
      (A.twist χ.toMonoidHom χ.isOpen_ker)) ↔
      IsZero ((normalizedJacquetFunctor U M hU hMU).obj A) := by
  rw [SmoothRep.isZero_iff_subsingleton_carrier,
    SmoothRep.isZero_iff_subsingleton_carrier]
  exact (normalizedJacquetCharacterTwistEquiv U M hU hMU χ hχU A).toEquiv.subsingleton_congr

end Jacquet

section Cuspidality

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}
  (P M U : Finset ι → Subgroup G) (J : Finset ι) (hM : IsClosed (M J : Set G))
  (hJ : ∀ I : Finset J, IsSemidirectDecomposition
    ((P (leviIndex J I)).subgroupOf (M J))
    ((M (leviIndex J I)).subgroupOf (M J))
    ((U (leviIndex J I)).subgroupOf (M J)))
  (hU : ∀ I, IsClosed (U I : Set G))

/-- Cuspidality in the actual Levi is unchanged by a smooth character killing
its proper standard radicals. -/
theorem isCorollaryLeviCuspidal_characterTwist_iff
    (χ : Induction.SmoothCharacter ℂ (M J))
    (hχU : ∀ I : Finset J, I ≠ Finset.univ →
      (U (leviIndex J I)).subgroupOf (M J) ≤ χ.toMonoidHom.ker)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    IsCorollaryLeviCuspidal P M U J hM hJ hU
        (A.twist χ.toMonoidHom χ.isOpen_ker) ↔
      IsCorollaryLeviCuspidal P M U J hM hJ hU A := by
  let := hM.locallyCompactSpace
  constructor
  · intro hc I hI
    exact (normalizedJacquet_isZero_characterTwist_iff _ _
      ((hU (leviIndex J I)).preimage continuous_subtype_val)
      (hJ I).levi_le_normalizer χ (hχU I hI) A).mp (hc I hI)
  · intro hc I hI
    exact (normalizedJacquet_isZero_characterTwist_iff _ _
      ((hU (leviIndex J I)).preimage continuous_subtype_val)
      (hJ I).levi_le_normalizer χ (hχU I hI) A).mpr (hc I hI)

end Cuspidality

end Langlands.Aubert.General
