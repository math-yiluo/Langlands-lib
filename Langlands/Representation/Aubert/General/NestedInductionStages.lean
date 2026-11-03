import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Induction.SmoothTransitivity
import Langlands.Representation.Induction.SmoothSplitQuotient
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences

/-! Normalized induction in stages for actual nested semidirect subgroups. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

namespace NestedInduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M N Q L U : Subgroup G}
  (hP : IsSemidirectDecomposition P M N)
  (hQ : IsSemidirectDecomposition Q L U)
  (hL : IsClosed (L : Set G)) (hML : M ≤ L)
  (hInner : IsSemidirectDecomposition
    (P.subgroupOf L) (M.subgroupOf L) (N.subgroupOf L))
  (hN : IsClosed (N : Set G)) (hU : IsClosed (U : Set G))
  (hPQ : P ≤ Q) (hUN : U ≤ N)
  (hproj : Continuous hQ.projection)
  (hδN : IsUnimodularModulus N hN)
  (hδU : IsUnimodularModulus U hU)

local notation "φ" => (MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hPQ))
local notation "s" => Subgroup.inclusion hQ.levi_le
local notation "r" => hQ.projection

include hP hUN in
omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
private theorem ker_le : (hQ.projection).ker ≤ P.subgroupOf Q := by
  intro q hq
  exact hP.unipotent_le (hUN ((hQ.projection_eq_one_iff q).mp hq))

include hUN hδN in
private theorem coefficient_kernel
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (p : P.subgroupOf Q) (hp : r (p : Q) = 1) (v : A) :
    (inducingRepresentation hP hN A).comp φ p v = v := by
  have hu : ((p : Q) : G) ∈ U := (hQ.projection_eq_one_iff _).mp hp
  have hn : ((p : Q) : G) ∈ N := hUN hu
  change ((HaarModulus.closedHalfCharacter N hN P hP.le_normalizer (φ p) : ℂˣ) : ℂ) •
    A.representation (hP.projection (φ p)) v = v
  rw [show hP.projection (φ p) = 1 from (hP.projection_eq_one_iff _).mpr hn]
  rw [show HaarModulus.closedHalfCharacter N hN P hP.le_normalizer (φ p) = 1 from
    closedHalfCharacter_unipotent hP hN hδN ⟨_, hn⟩]
  simp

private def outerLeviCharacter : Induction.SmoothCharacter ℂ L :=
  inductionCharacter U L hU hQ.levi_le_normalizer

private def innerCoefficient (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation ℂ (P.subgroupOf L) A :=
  letI := hL.locallyCompactSpace
  inducingRepresentation hInner (hN.preimage continuous_subtype_val)
    ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hML)).obj A)

/-- The half-character product on the literal inner parabolic. -/
def HalfCharacterProduct : Prop :=
  letI := hL.locallyCompactSpace
  ∀ p : P.subgroupOf L,
    HaarModulus.closedHalfCharacter N hN P hP.le_normalizer
        ⟨((p : L) : G), p.property⟩ =
      HaarModulus.closedHalfCharacter U hU L hQ.levi_le_normalizer (p : L) *
        HaarModulus.closedHalfCharacter (N.subgroupOf L)
          (hN.preimage continuous_subtype_val) (P.subgroupOf L)
          hInner.le_normalizer p

private theorem coefficient_restrict
    (hχ : HalfCharacterProduct hP hQ hL hInner hN hU)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((inducingRepresentation hP hN A).comp φ).comp
        ((Subgroup.inclusion hQ.levi_le).subgroupComap (P.subgroupOf Q)) =
      Langlands.twist
        ((outerLeviCharacter hQ hU).toMonoidHom.comp (P.subgroupOf L).subtype)
        (innerCoefficient hL hML hInner hN A) := by
  let := hL.locallyCompactSpace
  ext p v
  change ((HaarModulus.closedHalfCharacter N hN P hP.le_normalizer
      ⟨((p : L) : G), p.property⟩ : ℂˣ) : ℂ) •
      A.representation (hP.projection ⟨((p : L) : G), p.property⟩) v =
    ((HaarModulus.closedHalfCharacter U hU L hQ.levi_le_normalizer (p : L) : ℂˣ) : ℂ) •
      (((HaarModulus.closedHalfCharacter (N.subgroupOf L)
          (hN.preimage continuous_subtype_val) (P.subgroupOf L)
          hInner.le_normalizer p : ℂˣ) : ℂ) •
        A.representation
          (subgroupOfContinuousEquiv hML (hInner.projection p)) v)
  rw [hχ p, Units.val_mul, mul_smul]
  congr 2
  exact congrArg (fun m : M => A.representation m v)
    (IsSemidirectDecomposition.projection_subgroupOf hP hInner p).symm

include hδU in
private theorem outer_twist_eq (A : SmoothRep.{0, uG, uV} ℂ M) :
    (Langlands.twist (outerLeviCharacter hQ hU).toMonoidHom
        (Induction.smoothInduced (P.subgroupOf L)
          (innerCoefficient hL hML hInner hN A))).comp r =
      inducingRepresentation hQ hU
        ((leviNormalizedInductionFunctor hL hML hInner hN).obj A) := by
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro f
  change ((HaarModulus.closedHalfCharacter U hU L hQ.levi_le_normalizer (r q) : ℂˣ) : ℂ) •
      Induction.smoothInduced (P.subgroupOf L)
        (innerCoefficient hL hML hInner hN A) (r q) f =
    ((HaarModulus.closedHalfCharacter U hU Q hQ.le_normalizer q : ℂˣ) : ℂ) •
      Induction.smoothInduced (P.subgroupOf L)
        (innerCoefficient hL hML hInner hN A) (r q) f
  rw [closedHalfCharacter_eq_comp_projection hQ hU hδU]
  rfl

private def middleEquiv
    (hχ : HalfCharacterProduct hP hQ hL hInner hN hU)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      (Induction.smoothInduced (P.subgroupOf Q)
        ((inducingRepresentation hP hN A).comp φ))
      (inducingRepresentation hQ hU
        ((leviNormalizedInductionFunctor hL hML hInner hN).obj A)) := by
  let e₁ := Induction.smoothSplitQuotientEquiv r hproj s
    (continuous_subtype_val.subtype_mk _) hQ.projection_levi
    (P.subgroupOf Q) (ker_le hP hQ hUN)
    ((inducingRepresentation hP hN A).comp φ)
    (coefficient_kernel hP hQ hN hPQ hUN hδN A)
  let e₂ := Induction.smoothInducedEquiv (P.subgroupOf L)
    (equivOfRepresentationEq (coefficient_restrict hP hQ hL hML hInner hN hU hPQ hχ A))
  let e₃ := (Induction.smoothInductionTwistEquiv (P.subgroupOf L)
    (outerLeviCharacter hQ hU) (innerCoefficient hL hML hInner hN A)).symm
  exact ((e₁.trans (CuspidalSupport.equivComp e₂ r)).trans
      (CuspidalSupport.equivComp e₃ r)).trans
    (equivOfRepresentationEq (outer_twist_eq hQ hL hML hInner hN hU hδU A))

/-- The actual normalized induced representations agree in stages. -/
def equiv
    (hχ : HalfCharacterProduct hP hQ hL hInner hN hU)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      (((normalizedInductionFunctor hP hN).obj A).representation)
      (((leviNormalizedInductionFunctor hL hML hInner hN ⋙
          normalizedInductionFunctor.{uG, max uG uV} hQ hU).obj A).representation) :=
  (Induction.smoothStagesEquiv P Q hPQ (inducingRepresentation hP hN A)).symm.trans
    (Induction.smoothInducedEquiv Q
      (middleEquiv hP hQ hL hML hInner hN hU hPQ hUN hproj hδN hδU hχ A))

/-- The comparison expands a direct function and removes the outer character. -/
@[simp] theorem equiv_eval
    (hχ : HalfCharacterProduct hP hQ hL hInner hN hU)
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor hP hN).obj A) (x : G) (l : L) :
    ((equiv hP hQ hL hML hInner hN hU hPQ hUN hproj hδN hδU hχ A f).1.1 x).1.1 l =
      ((HaarModulus.closedHalfCharacter U hU L hQ.levi_le_normalizer l)⁻¹ : ℂˣ) •
        f.1.1 ((l : G) * x) := by
  rfl

/-- The actual coefficient maps commute with normalized induction in stages. -/
theorem equiv_natural
    (hχ : HalfCharacterProduct hP hQ hL hInner hN hU)
    {A B : SmoothRep.{0, uG, uV} ℂ M} (T : A ⟶ B)
    (f : (normalizedInductionFunctor hP hN).obj A) :
    equiv hP hQ hL hML hInner hN hU hPQ hUN hproj hδN hδU hχ B
        (SmoothRep.hom ((normalizedInductionFunctor hP hN).map T) f) =
      SmoothRep.hom
        ((leviNormalizedInductionFunctor hL hML hInner hN ⋙
          normalizedInductionFunctor.{uG, max uG uV} hQ hU).map T)
        (equiv hP hQ hL hML hInner hN hU hPQ hUN hproj hδN hδU hχ A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  apply Subtype.ext
  apply Subtype.ext
  funext l
  change (((HaarModulus.closedHalfCharacter U hU L hQ.levi_le_normalizer l)⁻¹ : ℂˣ) : ℂ) •
      SmoothRep.hom T (f.1.1 ((l : G) * x)) =
    SmoothRep.hom T
      ((((HaarModulus.closedHalfCharacter U hU L hQ.levi_le_normalizer l)⁻¹ : ℂˣ) : ℂ) •
        f.1.1 ((l : G) * x))
  exact (map_smul (SmoothRep.hom T) _ _).symm

/-- Normalized induction in stages on the full smooth categories. -/
def iso
    (hχ : HalfCharacterProduct hP hQ hL hInner hN hU) :
    normalizedInductionFunctor.{uG, uV} hP hN ≅
      leviNormalizedInductionFunctor.{uG, uV} hL hML hInner hN ⋙
        normalizedInductionFunctor.{uG, max uG uV} hQ hU :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (equiv hP hQ hL hML hInner hN hU hPQ hUN hproj hδN hδU hχ A))
    (fun {A B} T => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro f
      exact equiv_natural hP hQ hL hML hInner hN hU hPQ hUN hproj hδN hδU hχ T f)

end NestedInduction

end Langlands.Aubert.General
