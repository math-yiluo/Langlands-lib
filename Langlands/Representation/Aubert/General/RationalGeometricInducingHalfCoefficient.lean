import Langlands.Representation.Aubert.General.RationalGeometricLocalizedCoefficient
import Langlands.Representation.Aubert.General.DynamicNestedParabolicTopology
import Langlands.Representation.Aubert.General.JacquetStages
import Langlands.Representation.Jacquet.CharacterTwistEquiv

/-! # The original inducing half-character on the actual coefficient quotient -/

noncomputable section

universe u uG uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section CompactLimit

variable {A : Type uG} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- Compact-subgroup containment survives conjugation and intersection with
a closed subgroup, including the literal copy inside that subgroup. -/
theorem isLimitOfCompactSubgroups_geometricSourceIntersection
    (U M : Subgroup A) (n : A) (hM : IsClosed (M : Set A))
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((geometricSourceIntersection U M n).subgroupOf M) := by
  change Jacquet.Localization.IsLimitOfCompactSubgroups
    ((M ⊓ U.map (MulAut.conj n⁻¹ : A →* A)).subgroupOf M)
  rw [Subgroup.inf_subgroupOf_left]
  apply isLimitOfCompactSubgroups_subgroupOf _ M hM
  let e : U.map (MulAut.conj n⁻¹ : A →* A) ≃ₜ* U :=
    conjugationEquiv n⁻¹ (fun _ => Subgroup.mem_map_equiv)
  exact compactLimit_of_closedEmbedding _ _ e.toMonoidHom
    e.toHomeomorph.isClosedEmbedding hU

end CompactLimit

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection (levi i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "χ" => HaarModulus.closedHalfCharacter
  (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer

include hMJ hUc in
/-- The actual inducing modulus is trivial on the inverse-conjugate target
radical inside the original source Levi. -/
theorem geometricInducingModulus_eq_one (s : S) :
    HaarModulus.closedRestrictCharacter
      (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer s = 1 :=
  positiveCharacter_eq_one_on_compactLimit _
    (HaarModulus.isOpen_ker_closedRestrictCharacter
      (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer) S
    (isLimitOfCompactSubgroups_geometricSourceIntersection _ _
      (n : RationalPoint k G.X) hMJ hUc) s

include hMJ hUc in
/-- The original canonical positive half-character is trivial on that radical. -/
theorem geometricInducingHalfCharacter_eq_one (s : S) : χ s = 1 := by
  have hδ := geometricInducingModulus_eq_one i ν I J dJ n hUJ hMJ hUc s
  simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, hδ, map_one]

include hMJ hUc in
/-- Kernel containment needed for the actual character-twisted Jacquet quotient. -/
theorem geometricSourceRadical_le_ker_inducingHalfCharacter : S ≤ (χ).ker := by
  intro s hs
  exact geometricInducingHalfCharacter_eq_one i ν I J dJ n hUJ hMJ hUc ⟨s, hs⟩

variable
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (levi i ν I)
local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (parabolic i ν I)
local notation "N" => Subgroup.comap (Subgroup.subtype H) (MonoidHom.ker dI.projection)
local notation "f" => geometricCoefficientProjection
  (parabolic i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  dJ (n : RationalPoint k G.X)
local notation "p" => geometricCoefficientLeviMap
  (levi i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget

/-- The ordinary source Jacquet action with the original inducing half,
restricted and inflated through the actual intersection projection. -/
abbrev geometricInducingHalfSourceCoefficientAction
    (σ : Representation ℂ (levi i ν J) V) :
    Representation ℂ K (Jacquet.Coinvariants σ S) :=
  twist (((χ).comp (Subgroup.subtype Ls)).comp p)
    ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p)

/-- The original positive inducing half passes through the actual localized
coefficient quotient. The map preserves every original vector class. -/
def geometricInducingHalfCoefficientEquiv (σ : Representation ℂ (levi i ν J) V) :
    (geometricLocalizedCoefficientAction i ν I J dI dJ n (twist χ σ)).Equiv
      (geometricInducingHalfSourceCoefficientAction i ν I J dJ n hUJ
        hSource hTarget σ) :=
  (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget (twist χ σ)).trans
      { toLinearEquiv := (Jacquet.actionTwistEquiv σ S Ls hSource.levi_le_normalizer χ
          (geometricSourceRadical_le_ker_inducingHalfCharacter
            i ν I J dJ n hUJ hMJ hUc)).toLinearEquiv
        isIntertwining' l := (Jacquet.actionTwistEquiv σ S Ls hSource.levi_le_normalizer χ
          (geometricSourceRadical_le_ker_inducingHalfCharacter
            i ν I J dJ n hUJ hMJ hUc)).isIntertwining' (p l) }

@[simp] theorem geometricInducingHalfCoefficientEquiv_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
        hStandard hG hi hν hN dI hSource hTarget σ
        (Jacquet.Localization.mk ((twist χ σ).comp f) N 1 v) =
      Jacquet.mk σ S v := by
  change Jacquet.actionTwistEquiv σ S Ls hSource.levi_le_normalizer χ
    (geometricSourceRadical_le_ker_inducingHalfCharacter i ν I J dJ n hUJ hMJ hUc)
    (geometricLocalizedCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget (twist χ σ) (Jacquet.Localization.mk ((twist χ σ).comp f) N 1 v)) = _
  rw [geometricLocalizedCoefficientEquiv_mk, Jacquet.actionTwistEquiv_mk]

@[simp] theorem geometricInducingHalfCoefficientEquiv_symm_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    (geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
        hStandard hG hi hν hN dI hSource hTarget σ).symm (Jacquet.mk σ S v) =
      Jacquet.Localization.mk ((twist χ σ).comp f) N 1 v := by
  exact (geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
    hStandard hG hi hν hN dI hSource hTarget σ).toLinearEquiv.symm_apply_eq.mpr
      (geometricInducingHalfCoefficientEquiv_mk i ν I J dJ n hUJ hMJ hUc
        hStandard hG hi hν hN dI hSource hTarget σ v).symm

set_option maxHeartbeats 800000 in
/-- The inducing-half comparison commutes with every original coefficient map. -/
theorem geometricInducingHalfCoefficientEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ)
    (z : Jacquet.Localization.Coinvariants ((twist χ σ).comp f) N 1) :
    geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
        hStandard hG hi hν hN dI hSource hTarget τ
        (Jacquet.Localization.mapLinear N 1
          (geometricCoefficientIntertwiner i ν I J dJ n (twistIntertwining χ a)) z) =
      Jacquet.map S Ls hSource.levi_le_normalizer a
        (geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
          hStandard hG hi hν hN dI hSource hTarget σ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ((twist χ σ).comp f) N 1 z
  change geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
      hStandard hG hi hν hN dI hSource hTarget τ
      (Jacquet.Localization.mk ((twist χ τ).comp f) N 1 (a v)) = _
  rw [geometricInducingHalfCoefficientEquiv_mk, geometricInducingHalfCoefficientEquiv_mk]
  rfl

section Smooth

variable (hproj : Continuous dJ.projection)

include hproj in
/-- The original inducing half gives a smooth actual localized coefficient action. -/
theorem isSmooth_geometricInducingHalfLocalizedCoefficientAction
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ) :
    IsSmooth (geometricLocalizedCoefficientAction i ν I J dI dJ n (twist χ σ)) :=
  isSmooth_geometricLocalizedCoefficientAction i ν I J dI dJ n hproj (twist χ σ)
    ((HaarModulus.isSmooth_twist_closedHalfCharacter_iff
      (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ)

include hStandard hG hi hν hN dI hMJ hUc hproj in
/-- Smoothness passes to the actual source coefficient with its restricted half. -/
theorem isSmooth_geometricInducingHalfSourceCoefficientAction
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ) :
    IsSmooth (geometricInducingHalfSourceCoefficientAction i ν I J dJ n hUJ
      hSource hTarget σ) :=
  isSmooth_of_surjective
    (geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
      hStandard hG hi hν hN dI hSource hTarget σ).toIntertwiningMap
    (geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
      hStandard hG hi hν hN dI hSource hTarget σ).surjective
    (isSmooth_geometricInducingHalfLocalizedCoefficientAction i ν I J dJ n hUJ dI
      hproj σ hσ)

/-- The class-preserving inducing-half comparison on the original smooth carriers. -/
def geometricInducingHalfCoefficientSmoothIso (σ : SmoothRep ℂ (levi i ν J)) :
    SmoothRep.of (geometricLocalizedCoefficientAction i ν I J dI dJ n
        (twist χ σ.representation))
        (isSmooth_geometricInducingHalfLocalizedCoefficientAction i ν I J dJ n hUJ dI
          hproj σ.representation σ.isSmooth) ≅
      SmoothRep.of (geometricInducingHalfSourceCoefficientAction i ν I J dJ n hUJ
        hSource hTarget σ.representation)
        (isSmooth_geometricInducingHalfSourceCoefficientAction i ν I J dJ n hUJ hMJ hUc
          hStandard hG hi hν hN dI hSource hTarget hproj σ.representation σ.isSmooth) :=
  SmoothRep.mkIso (geometricInducingHalfCoefficientEquiv i ν I J dJ n hUJ hMJ hUc
    hStandard hG hi hν hN dI hSource hTarget σ.representation)

end Smooth
end RationalPointFamily
end Langlands.Aubert.General
