import Langlands.Representation.Aubert.General.RationalGeometricCorrections
import Langlands.Representation.Aubert.General.RationalGeometricCorrectionFactorization
import Langlands.Representation.Aubert.General.Conjugation

/-! # Forward transport and factorization of the original epsilon corrections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General

section Ambient

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A]
  (MI MJ : Subgroup A) (n : A)

local notation "L" => geometricTargetIntersection MI MJ n
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ n) MI
local notation "flat" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe
  (inf_le_left : geometricTargetIntersection MI MJ n ≤ MI))

/-- The Haar modulus on an actual forward-conjugate intersection, restricted
to the literal nested common Levi without changing its ambient point. -/
def geometricCommonLeviIntersectionModulus (U V : Subgroup A)
    (hU : IsClosed (U : Set A)) (hV : IsClosed (V : Set A))
    (hMIU : MI ≤ Subgroup.normalizer U) (hMJV : MJ ≤ Subgroup.normalizer V) :
    Lt →* ℝ≥0ˣ :=
  (HaarModulus.closedRestrictCharacter
    (geometricTargetIntersection U V n)
    (isClosed_geometricTargetIntersection U V hU hV n) L
    (geometricCommonLevi_normalizes_intersection MI MJ U V n hMIU hMJV)).comp flat

/-- The original source-radical modulus expressed on the forward-conjugate
radical at the same target common-Levi point. -/
def geometricForwardSourceRadicalModulus (UJ : Subgroup A)
    (hUJ : IsClosed (UJ : Set A)) (hMJUJ : MJ ≤ Subgroup.normalizer UJ) :
    Lt →* ℝ≥0ˣ :=
  (HaarModulus.closedRestrictCharacter
    (UJ.map (MulAut.conj n).toMonoidHom) (isClosed_map_conj UJ hUJ n) L
    (inf_le_right.trans
      ((Subgroup.map_mono hMJUJ).trans (Subgroup.le_normalizer_map _)))).comp flat

theorem geometricSourceCorrectionRadicalModulus_eq_forward
    (UJ : Subgroup A) (hUJ : IsClosed (UJ : Set A))
    (hMJUJ : MJ ≤ Subgroup.normalizer UJ) :
    geometricSourceCorrectionRadicalModulus MI MJ n UJ hUJ hMJUJ =
      geometricForwardSourceRadicalModulus MI MJ n UJ hUJ hMJUJ := by
  apply MonoidHom.ext
  intro l
  let x : Subgroup.normalizer
      (UJ.map (MulAut.conj n).toMonoidHom : Set A) :=
    ⟨l.val.val, (inf_le_right.trans
      ((Subgroup.map_mono hMJUJ).trans (Subgroup.le_normalizer_map _)))
        (flat l).property⟩
  let y := Geometric.General.intersectionToRadicalNormalizer
    MJ MI UJ n hMJUJ (geometricSourceCorrectionTransport MI MJ n l)
  have hxy : (y : A) = n⁻¹ * (x : A) * n :=
    geometricSourceCorrectionTransport_apply MI MJ n l
  have hy : n⁻¹ * (x : A) * n ∈ Subgroup.normalizer (UJ : Set A) := by
    rw [← hxy]
    exact y.property
  have hmem : ∀ a : A, a ∈ UJ.map (MulAut.conj n).toMonoidHom ↔
      n⁻¹ * a * n ∈ UJ := by
    intro a
    rw [Subgroup.mem_map_equiv]
    rfl
  have h := closedNormalizerCharacter_conj n hmem
    hUJ (isClosed_map_conj UJ hUJ n) x hy
  change HaarModulus.closedNormalizerCharacter UJ hUJ y =
    HaarModulus.closedNormalizerCharacter
      (UJ.map (MulAut.conj n).toMonoidHom) (isClosed_map_conj UJ hUJ n) x
  rw [h]
  congr 1
  exact Subtype.ext hxy

/-- Forward conjugation of the source correction subgroup is the literal
intersection `PI ∩ n UJ n⁻¹`, including its original acting point. -/
theorem geometricSourceCorrectionIntersectionModulus_eq_forward
    (PI UJ : Subgroup A)
    (hPI : IsClosed (PI : Set A)) (hUJ : IsClosed (UJ : Set A))
    (hMIPI : MI ≤ Subgroup.normalizer PI) (hMJUJ : MJ ≤ Subgroup.normalizer UJ) :
    geometricSourceCorrectionIntersectionModulus MI MJ n PI UJ hUJ hPI hMJUJ hMIPI =
      geometricCommonLeviIntersectionModulus MI MJ n PI UJ hPI hUJ hMIPI hMJUJ := by
  apply MonoidHom.ext
  intro l
  let x : Subgroup.normalizer (geometricTargetIntersection PI UJ n : Set A) :=
    ⟨l.val.val,
      geometricCommonLevi_normalizes_intersection MI MJ PI UJ n hMIPI hMJUJ
        (flat l).property⟩
  let y := Geometric.General.intersectionToCorrectionNormalizer
    MJ MI UJ PI n hMJUJ hMIPI (geometricSourceCorrectionTransport MI MJ n l)
  have hxy : (y : A) = n⁻¹ * (x : A) * n :=
    geometricSourceCorrectionTransport_apply MI MJ n l
  have hy : n⁻¹ * (x : A) * n ∈ Subgroup.normalizer
      (Geometric.intersectionSource UJ PI n : Set A) := by
    rw [← hxy]
    exact y.property
  have hmem : ∀ a : A, a ∈ geometricTargetIntersection PI UJ n ↔
      n⁻¹ * a * n ∈ Geometric.intersectionSource UJ PI n := by
    intro a
    simp only [mem_geometricTargetIntersection,
      Geometric.General.mem_correctionSubgroup]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    exact and_comm
  have h := closedNormalizerCharacter_conj n hmem
    (Geometric.General.isClosed_correctionSubgroup UJ PI n hUJ hPI)
    (isClosed_geometricTargetIntersection PI UJ hPI hUJ n) x hy
  change HaarModulus.closedNormalizerCharacter
      (Geometric.intersectionSource UJ PI n)
      (Geometric.General.isClosed_correctionSubgroup UJ PI n hUJ hPI) y =
    HaarModulus.closedNormalizerCharacter
      (geometricTargetIntersection PI UJ n)
      (isClosed_geometricTargetIntersection PI UJ hPI hUJ n) x
  rw [h]
  congr 1
  exact Subtype.ext hxy

/-- The target correction uses the same ambient point on its literal
forward-conjugate correction intersection. -/
theorem geometricTargetCorrectionIntersectionModulus_eq_forward
    (UI PJ : Subgroup A)
    (hUI : IsClosed (UI : Set A)) (hPJ : IsClosed (PJ : Set A))
    (hMIUI : MI ≤ Subgroup.normalizer UI) (hMJPJ : MJ ≤ Subgroup.normalizer PJ) :
    geometricTargetCorrectionIntersectionModulus MI MJ n UI PJ hUI hPJ hMIUI hMJPJ =
      geometricCommonLeviIntersectionModulus MI MJ n UI PJ hUI hPJ hMIUI hMJPJ := by
  apply MonoidHom.ext
  intro l
  apply geometricTargetCorrectionIntersectionModulus_eq_ambient
    MI MJ UI PJ n hUI hPJ hMIUI hMJPJ l
  rfl

end Ambient

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)] [SecondCountableTopology (RationalPoint k G.X)]
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))

local notation "A" => RationalPoint k G.X
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "L" => geometricTargetIntersection MI MJ (n : A)
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ (n : A)) MI
local notation "hMIPI" => dI.levi_le.trans (fun _ hx => Subgroup.le_normalizer hx)
local notation "hMIMI" => (fun _ hx => Subgroup.le_normalizer hx : MI ≤ Subgroup.normalizer MI)
local notation "deltaB" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  MI UJ hMI hUJ hMIMI dJ.levi_le_normalizer
local notation "deltaC" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  UI UJ hUI hUJ dI.levi_le_normalizer dJ.levi_le_normalizer
local notation "deltaV" => geometricForwardSourceRadicalModulus MI MJ (n : A)
  UJ hUJ dJ.levi_le_normalizer

include hStandard hG hi hν hN dI

/-- The original source correction-subgroup modulus factors into the actual
target endpoint radical and the actual common unipotent intersection. -/
theorem geometricEpsilonOne_correctionModulus_eq_mul (hp : Continuous dI.projection) :
    geometricSourceCorrectionIntersectionModulus MI MJ (n : A)
        PI UJ hUJ hPI dJ.levi_le_normalizer hMIPI =
      deltaB * deltaC := by
  rw [geometricSourceCorrectionIntersectionModulus_eq_forward]
  have h := geometricCorrectionIntersection_modulus_eq_mul
    i ν hStandard hG hi hν hN I J dI n dJ hPI hMI hUI hUJ hp
  apply MonoidHom.ext
  intro l
  exact congrArg (fun f : L →* ℝ≥0ˣ =>
    f ((Subgroup.subgroupOfEquivOfLe
      (inf_le_left : geometricTargetIntersection MI MJ (n : A) ≤ MI)) l)) h

/-- The original source epsilon has its canonical positive source-radical
half and both inverse intersection halves, on the whole literal common Levi. -/
theorem geometricEpsilonOne_eq_factorized_half (hp : Continuous dI.projection) :
    geometricEpsilonOne i ν I J dI dJ n hUJ hPI =
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaV) *
        Jacquet.inverseHalfCharacter deltaB * Jacquet.inverseHalfCharacter deltaC := by
  unfold geometricEpsilonOne
  rw [geometricSourceCorrectionCharacter_eq,
    geometricSourceCorrectionRadicalModulus_eq_forward,
    geometricEpsilonOne_correctionModulus_eq_mul
      i ν hStandard hG hi hν hN I J dI dJ n hPI hMI hUI hUJ hp]
  apply MonoidHom.ext
  intro l
  simp only [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, MonoidHom.mul_apply,
    MonoidHom.inv_apply, map_mul, mul_inv, mul_assoc]

end RationalPointFamily

end Langlands.Aubert.General
