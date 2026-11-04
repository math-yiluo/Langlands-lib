import Langlands.Representation.Aubert.General.GeometricCoefficientAction
import Langlands.Representation.Geometric.GeneralCorrectionCharacters

/-! # Both original Haar corrections on the literal common Levi -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Aubert.General

universe uG uV

variable {A : Type uG} [Group A] (MI MJ : Subgroup A) (n : A)

local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ n) MI

/-- Equality transport from the literal target common Levi to the original
BZ target intersection; the underlying ambient point is unchanged. -/
def geometricTargetCorrectionTransport :
    Lt →* Geometric.General.intersectionIn MI MJ n⁻¹ :=
  (MulEquiv.subgroupCongr
    (intersectionIn_inv_eq_geometricTarget_subgroupOf MI MJ n).symm).toMonoidHom

/-- Inverse conjugation from the literal target common Levi to the original
BZ source intersection. -/
def geometricSourceCorrectionTransport :
    Lt →* Geometric.General.intersectionIn MJ MI n :=
  (MulEquiv.subgroupCongr
    (intersectionIn_eq_geometricSource_subgroupOf MI MJ n).symm).toMonoidHom.comp
      (geometricIntersectionSubgroupEquiv MI MJ n).toMonoidHom

@[simp] theorem geometricTargetCorrectionTransport_apply (l : Lt) :
    (geometricTargetCorrectionTransport MI MJ n l).val.val = l.val.val := rfl

@[simp] theorem geometricSourceCorrectionTransport_apply (l : Lt) :
    (geometricSourceCorrectionTransport MI MJ n l).val.val = n⁻¹ * l.val.val * n :=
  geometricIntersectionSubgroupEquiv_apply MI MJ n l

/-- The source correction uses precisely the inverse of the original BZ
intersection conjugation, after the target equality transport. -/
theorem geometricSourceCorrectionTransport_eq (l : Lt) :
    geometricSourceCorrectionTransport MI MJ n l =
      (Geometric.General.intersectionEquiv MJ MI n).symm
        (geometricTargetCorrectionTransport MI MJ n l) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [geometricSourceCorrectionTransport_apply,
    Geometric.General.intersectionEquiv_symm_apply,
    geometricTargetCorrectionTransport_apply]

section Topology

variable [TopologicalSpace A]

theorem continuous_geometricTargetCorrectionTransport :
    Continuous (geometricTargetCorrectionTransport MI MJ n) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

variable [IsTopologicalGroup A]

theorem continuous_geometricSourceCorrectionTransport :
    Continuous (geometricSourceCorrectionTransport MI MJ n) := by
  have h : Continuous (fun l : Lt =>
      n⁻¹ * l.val.val * n) :=
    (continuous_const.mul
      (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const
  exact ((h.congr (fun l =>
    (geometricSourceCorrectionTransport_apply MI MJ n l).symm)).subtype_mk _).subtype_mk _

end Topology

section Haar

variable [TopologicalSpace A] [LocallyCompactSpace A]
  (PI UI PJ UJ : Subgroup A)
  (hUI : IsClosed (UI : Set A)) (hUJ : IsClosed (UJ : Set A))
  (hPI : IsClosed (PI : Set A)) (hPJ : IsClosed (PJ : Set A))
  (hMIUI : MI ≤ Subgroup.normalizer UI)
  (hMJUJ : MJ ≤ Subgroup.normalizer UJ)
  (hMIPI : MI ≤ Subgroup.normalizer PI)
  (hMJPJ : MJ ≤ Subgroup.normalizer PJ)

section Characters

variable [IsTopologicalGroup A]

/-- Original source-radical modulus, pulled back along `n⁻¹ x n`. -/
def geometricSourceCorrectionRadicalModulus : Lt →* ℝ≥0ˣ :=
  (Geometric.General.intersectionRadicalModulus MJ MI UJ n hUJ hMJUJ).comp
    (geometricSourceCorrectionTransport MI MJ n)

/-- Original source correction-subgroup modulus, with the same pullback. -/
def geometricSourceCorrectionIntersectionModulus : Lt →* ℝ≥0ˣ :=
  (Geometric.General.intersectionCorrectionModulus MJ MI UJ PI n
    hUJ hPI hMJUJ hMIPI).comp (geometricSourceCorrectionTransport MI MJ n)

/-- Original target-radical modulus on the literal common Levi. -/
def geometricTargetCorrectionRadicalModulus : Lt →* ℝ≥0ˣ :=
  (Geometric.General.intersectionRadicalModulus MI MJ UI n⁻¹ hUI hMIUI).comp
    (geometricTargetCorrectionTransport MI MJ n)

/-- Original target correction-subgroup modulus on the literal common Levi. -/
def geometricTargetCorrectionIntersectionModulus : Lt →* ℝ≥0ˣ :=
  (Geometric.General.intersectionCorrectionModulus MI MJ UI PJ n⁻¹
    hUI hPJ hMIUI hMJPJ).comp (geometricTargetCorrectionTransport MI MJ n)

/-- BZ's source correction `ε₁`, including both of its original half-moduli,
transported to the literal target common Levi by inverse conjugation. -/
def geometricSourceCorrectionCharacter : Lt →* ℂˣ :=
  (Geometric.General.haarCorrectionCharacter MJ MI UJ PI n
    hUJ hPI hMJUJ hMIPI).comp (geometricSourceCorrectionTransport MI MJ n)

/-- BZ's target correction `ε₂`, including both original half-moduli, moved
to the literal target common Levi by subgroup equality. -/
def geometricTargetCorrectionCharacter : Lt →* ℂˣ :=
  (Geometric.General.haarCorrectionCharacter MI MJ UI PJ n⁻¹
    hUI hPJ hMIUI hMJPJ).comp (geometricTargetCorrectionTransport MI MJ n)

theorem geometricSourceCorrectionCharacter_eq :
    geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI =
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
        (geometricSourceCorrectionRadicalModulus MI MJ n UJ hUJ hMJUJ)) *
      Jacquet.inverseHalfCharacter
        (geometricSourceCorrectionIntersectionModulus MI MJ n PI UJ hUJ hPI hMJUJ hMIPI) := rfl

theorem geometricTargetCorrectionCharacter_eq :
    geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ =
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
        (geometricTargetCorrectionRadicalModulus MI MJ n UI hUI hMIUI)) *
      Jacquet.inverseHalfCharacter
        (geometricTargetCorrectionIntersectionModulus MI MJ n UI PJ hUI hPJ hMIUI hMJPJ) := rfl

theorem geometricSourceCorrectionCharacter_sq (l : Lt) :
    geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI l ^ 2 =
      Jacquet.complexCharacter
        (geometricSourceCorrectionRadicalModulus MI MJ n UJ hUJ hMJUJ) l /
      Jacquet.complexCharacter
        (geometricSourceCorrectionIntersectionModulus MI MJ n PI UJ hUJ hPI hMJUJ hMIPI) l := by
  exact Geometric.General.haarCorrectionCharacter_sq MJ MI UJ PI n hUJ hPI hMJUJ hMIPI
    (geometricSourceCorrectionTransport MI MJ n l)

theorem geometricTargetCorrectionCharacter_sq (l : Lt) :
    geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ l ^ 2 =
      Jacquet.complexCharacter
        (geometricTargetCorrectionRadicalModulus MI MJ n UI hUI hMIUI) l /
      Jacquet.complexCharacter
        (geometricTargetCorrectionIntersectionModulus MI MJ n UI PJ hUI hPJ hMIUI hMJPJ) l := by
  exact Geometric.General.haarCorrectionCharacter_sq MI MJ UI PJ n⁻¹ hUI hPJ hMIUI hMJPJ
    (geometricTargetCorrectionTransport MI MJ n l)

end Characters

section Smooth

variable [NonarchimedeanGroup A]

theorem isOpen_ker_geometricSourceCorrectionCharacter :
    IsOpen ((geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI).ker :
      Set Lt) :=
  (Geometric.General.isOpen_ker_haarCorrectionCharacter MJ MI UJ PI n
    hUJ hPI hMJUJ hMIPI).preimage
      (continuous_geometricSourceCorrectionTransport MI MJ n)

theorem isOpen_ker_geometricTargetCorrectionCharacter :
    IsOpen ((geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ).ker :
      Set Lt) :=
  (Geometric.General.isOpen_ker_haarCorrectionCharacter MI MJ UI PJ n⁻¹
    hUI hPJ hMIUI hMJPJ).preimage
      (continuous_geometricTargetCorrectionTransport MI MJ n)

/-- The first original correction as an actual smooth scalar character. -/
def geometricSourceCorrectionSmoothCharacter : Induction.SmoothCharacter ℂ Lt where
  toMonoidHom := geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI
  isOpen_ker :=
    isOpen_ker_geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI

/-- The second original correction as an actual smooth scalar character. -/
def geometricTargetCorrectionSmoothCharacter : Induction.SmoothCharacter ℂ Lt where
  toMonoidHom := geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ
  isOpen_ker :=
    isOpen_ker_geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ

/-- The transported source twist on the literal common Levi. -/
def geometricSourceCorrectionTwist :
    SmoothRep.{0, uG, uV} ℂ Lt ⥤ SmoothRep.{0, uG, uV} ℂ Lt :=
  SmoothRep.twistFunctor
    (geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI)
    (isOpen_ker_geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI)

/-- The transported target twist on the same literal common Levi. -/
def geometricTargetCorrectionTwist :
    SmoothRep.{0, uG, uV} ℂ Lt ⥤ SmoothRep.{0, uG, uV} ℂ Lt :=
  SmoothRep.twistFunctor
    (geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ)
    (isOpen_ker_geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ)

@[simp] theorem geometricSourceCorrectionTwist_action
    (σ : SmoothRep.{0, uG, uV} ℂ Lt) (l : Lt) (v : σ) :
    ((geometricSourceCorrectionTwist MI MJ n PI UJ hUJ hPI hMJUJ hMIPI).obj σ).representation
      l v =
      (geometricSourceCorrectionCharacter MI MJ n PI UJ hUJ hPI hMJUJ hMIPI l : ℂ) •
        σ.representation l v := rfl

@[simp] theorem geometricTargetCorrectionTwist_action
    (σ : SmoothRep.{0, uG, uV} ℂ Lt) (l : Lt) (v : σ) :
    ((geometricTargetCorrectionTwist MI MJ n UI PJ hUI hPJ hMIUI hMJPJ).obj σ).representation
      l v =
      (geometricTargetCorrectionCharacter MI MJ n UI PJ hUI hPJ hMIUI hMJPJ l : ℂ) •
        σ.representation l v := rfl

end Smooth
end Haar

end Langlands.Aubert.General
