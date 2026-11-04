import Langlands.Representation.Aubert.General.GeometricIntersectionCorrections
import Langlands.Representation.Aubert.General.RationalGeometricCompactHaar

/-! # Original epsilon corrections for the actual rational compact comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

section Ambient

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A]

private theorem closedNormalizerCharacter_eq_of_subgroup_eq
    (U V : Subgroup A) (hU : IsClosed (U : Set A)) (hV : IsClosed (V : Set A))
    (hUV : U = V)
    (x : Subgroup.normalizer (U : Set A)) (y : Subgroup.normalizer (V : Set A))
    (hxy : (x : A) = (y : A)) :
    HaarModulus.closedNormalizerCharacter U hU x =
      HaarModulus.closedNormalizerCharacter V hV y := by
  subst V
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Equality of the target BZ correction modulus with the original ambient
correction subgroup, at any normalizer point with the same ambient value. -/
theorem geometricTargetCorrectionIntersectionModulus_eq_ambient
    (MI MJ UI PJ : Subgroup A) (n : A)
    (hUI : IsClosed (UI : Set A)) (hPJ : IsClosed (PJ : Set A))
    (hMIUI : MI ≤ Subgroup.normalizer UI)
    (hMJPJ : MJ ≤ Subgroup.normalizer PJ)
    (l : (geometricTargetIntersection MI MJ n).subgroupOf MI)
    (x : Subgroup.normalizer (geometricTargetIntersection UI PJ n : Set A))
    (hx : (x : A) = l.val.val) :
    geometricTargetCorrectionIntersectionModulus MI MJ n UI PJ hUI hPJ hMIUI hMJPJ l =
      HaarModulus.closedNormalizerCharacter
        (geometricTargetIntersection UI PJ n)
        (isClosed_geometricTargetIntersection UI PJ hUI hPJ n) x := by
  have hEq :
      Geometric.intersectionSource UI PJ n⁻¹ = geometricTargetIntersection UI PJ n := by
    ext a
    simp only [Geometric.General.mem_correctionSubgroup,
      mem_geometricTargetIntersection, inv_inv]
  exact closedNormalizerCharacter_eq_of_subgroup_eq _ _
    (Geometric.General.isClosed_correctionSubgroup UI PJ n⁻¹ hUI hPJ)
    (isClosed_geometricTargetIntersection UI PJ hUI hPJ n) hEq _ _
    ((geometricTargetCorrectionTransport_apply MI MJ n l).trans hx.symm)

end Ambient

section Inclusion

variable {A : Type*} [Group A]

/-- Include the literal common Levi in the target intersection using its
original Levi containment. -/
def geometricCommonLeviInclusion (MI MJ PJ : Subgroup A) (hMJ : MJ ≤ PJ) (n : A) :
    (geometricTargetIntersection MI MJ n).subgroupOf MI →*
      (geometricTargetIntersection MI PJ n).subgroupOf MI :=
  Subgroup.inclusion (fun _ hl => ⟨hl.1, (Subgroup.map_mono hMJ) hl.2⟩)

@[simp] theorem geometricCommonLeviInclusion_apply
    (MI MJ PJ : Subgroup A) (hMJ : MJ ≤ PJ) (n : A)
    (l : (geometricTargetIntersection MI MJ n).subgroupOf MI) :
    (geometricCommonLeviInclusion MI MJ PJ hMJ n l).val.val = l.val.val := rfl

end Inclusion

namespace RationalPointFamily

universe u

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))

local notation "A" => RationalPoint k G.X
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "PJ" => parabolic i ν J
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "Lt" => Subgroup.subgroupOf
  (geometricTargetIntersection MI MJ (n : A)) MI
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection MI PJ (n : A)) MI
local notation "hMIPI" => dI.levi_le.trans (fun _ hx => Subgroup.le_normalizer hx)
local notation "hMJPJ" => dJ.levi_le.trans (fun _ hx => Subgroup.le_normalizer hx)

/-- Include the literal common Levi in the whole target intersection
parabolic, using the original inducing Levi containment. -/
def geometricCommonLeviInTarget : Lt →* K :=
  geometricCommonLeviInclusion MI MJ PJ dJ.levi_le (n : A)

@[simp] theorem geometricCommonLeviInTarget_apply (l : Lt) :
    (geometricCommonLeviInTarget i ν I J dJ n l).val.val = l.val.val :=
  geometricCommonLeviInclusion_apply MI MJ PJ dJ.levi_le (n : A) l

section Haar

variable [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))

section Characters

variable [IsTopologicalGroup (RationalPoint k G.X)]

/-- The actual original source epsilon correction, transported by `n⁻¹ x n`
to the literal target common Levi. -/
def geometricEpsilonOne : Lt →* ℂˣ :=
  geometricSourceCorrectionCharacter MI MJ (n : A) PI UJ hUJ hPI
    dJ.levi_le_normalizer hMIPI

/-- The actual original target epsilon correction on the same literal Levi. -/
def geometricEpsilonTwo : Lt →* ℂˣ :=
  geometricTargetCorrectionCharacter MI MJ (n : A) UI PJ hUI hPJ
    dI.levi_le_normalizer hMJPJ

local notation "c" => geometricCommonLeviInTarget i ν I J dJ n
local notation "δU" => geometricCompactRadicalModulus i ν I J dI n hUI
local notation "δC" => geometricCompactCorrectionModulus i ν I J dI n hUI hPJ

/-- The original target radical modulus is the restriction of the
whole-target radical modulus to the literal common Levi. -/
theorem geometricEpsilonTwo_radicalModulus_eq :
    geometricTargetCorrectionRadicalModulus MI MJ (n : A) UI hUI dI.levi_le_normalizer =
      (δU).comp c := by
  ext l
  rfl

/-- The original target correction-subgroup modulus restricts the exact
ambient correction modulus of the compact integral. -/
theorem geometricEpsilonTwo_correctionModulus_eq :
    geometricTargetCorrectionIntersectionModulus MI MJ (n : A) UI PJ hUI hPJ
        dI.levi_le_normalizer hMJPJ =
      (δC).comp c := by
  apply MonoidHom.ext
  intro l
  apply geometricTargetCorrectionIntersectionModulus_eq_ambient
    MI MJ UI PJ (n : A) hUI hPJ dI.levi_le_normalizer hMJPJ l
  exact geometricCommonLeviInTarget_apply i ν I J dJ n l

/-- The actual target epsilon is the canonical positive radical half times
the inverse correction half, restricted from the whole target parabolic. -/
theorem geometricEpsilonTwo_eq_half :
    geometricEpsilonTwo i ν I J dI dJ n hUI hPJ =
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) *
        Jacquet.inverseHalfCharacter δC).comp c := by
  unfold geometricEpsilonTwo
  rw [geometricTargetCorrectionCharacter_eq,
    geometricEpsilonTwo_radicalModulus_eq i ν I J dI dJ n hUI,
    geometricEpsilonTwo_correctionModulus_eq i ν I J dI dJ n hUI hPJ]
  rfl

variable
  [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernel i ν I J dI n)]
  [BorelSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernelIntersection i ν I J dI n)]
  [BorelSpace (geometricCompactKernelIntersection i ν I J dI n)]

/-- The square of the actual target epsilon is precisely the actual compact
integral character on the literal common Levi. -/
theorem geometricEpsilonTwo_sq (l : Lt) :
    geometricEpsilonTwo i ν I J dI dJ n hUI hPJ l ^ 2 =
      geometricCompactHaarCharacter i ν I J dI n hPI hPJ (c l) := by
  rw [geometricCompactHaarCharacter_eq_ambient i ν I J dI n hUI hPJ hPI]
  have h := geometricTargetCorrectionCharacter_sq MI MJ (n : A) UI PJ hUI hPJ
    dI.levi_le_normalizer hMJPJ l
  rw [geometricEpsilonTwo_radicalModulus_eq i ν I J dI dJ n hUI,
    geometricEpsilonTwo_correctionModulus_eq i ν I J dI dJ n hUI hPJ] at h
  exact h

end Characters

section Smooth

variable [NonarchimedeanGroup (RationalPoint k G.X)]

theorem isOpen_ker_geometricEpsilonOne :
    IsOpen ((geometricEpsilonOne i ν I J dI dJ n hUJ hPI).ker : Set Lt) :=
  isOpen_ker_geometricSourceCorrectionCharacter MI MJ (n : A) PI UJ hUJ hPI
    dJ.levi_le_normalizer hMIPI

theorem isOpen_ker_geometricEpsilonTwo :
    IsOpen ((geometricEpsilonTwo i ν I J dI dJ n hUI hPJ).ker : Set Lt) :=
  isOpen_ker_geometricTargetCorrectionCharacter MI MJ (n : A) UI PJ hUI hPJ
    dI.levi_le_normalizer hMJPJ

def geometricEpsilonOneSmoothCharacter : Induction.SmoothCharacter ℂ Lt where
  toMonoidHom := geometricEpsilonOne i ν I J dI dJ n hUJ hPI
  isOpen_ker := isOpen_ker_geometricEpsilonOne i ν I J dI dJ n hUJ hPI

def geometricEpsilonTwoSmoothCharacter : Induction.SmoothCharacter ℂ Lt where
  toMonoidHom := geometricEpsilonTwo i ν I J dI dJ n hUI hPJ
  isOpen_ker := isOpen_ker_geometricEpsilonTwo i ν I J dI dJ n hUI hPJ

end Smooth
end Haar

end RationalPointFamily
end Langlands.Aubert.General
