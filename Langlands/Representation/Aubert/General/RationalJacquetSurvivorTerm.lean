import Langlands.Representation.Aubert.General.LeviConjugation
import Langlands.Representation.Aubert.General.RationalJacquetStagesK0
import Langlands.Representation.Aubert.General.JacquetK0Assembly

/-! # The actual standard term in the rational Jacquet survivor -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

private theorem conjugatedStages
    {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (iS : D →ₗ[ℤ] B) (iT : E →ₗ[ℤ] C)
    (rS : B →ₗ[ℤ] D) (rJs : A →ₗ[ℤ] B) (rFine : A →ₗ[ℤ] D)
    (cM : B →ₗ[ℤ] C) (cL : D →ₗ[ℤ] E) (term : B →ₗ[ℤ] B)
    (hTransport : cM.comp iS = iT.comp cL)
    (hStages : rS.comp rJs = rFine)
    (hTerm : iS.comp rS = term) :
    iT.comp (cL.comp rFine) = cM.comp (term.comp rJs) := by
  calc
    _ = (iT.comp cL).comp (rS.comp rJs) := by rw [hStages]; rfl
    _ = (cM.comp iS).comp (rS.comp rJs) := by rw [hTransport]
    _ = cM.comp ((iS.comp rS).comp rJs) := rfl
    _ = _ := by rw [hTerm]

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})

local instance rationalSurvivorPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))

/-- Standard induction inside a coarse Levi, with the actual ambient
fine Levi as its source. -/
def standardLeviInductionK0 (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν (leviIndex J I)) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  LeviConjugation.inductionMap.{u, max (u + 1) v}
    (hM J)
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I)) (hLfl J I)

/-- Standard Jacquet restriction inside a coarse Levi, with its actual
ambient fine Levi as the target. -/
def standardLeviJacquetK0 (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν (leviIndex J I)) :=
  LeviConjugation.jacquetMap.{u, max (u + 1) v}
    (hM J)
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I)) (hLfl J I)

/-- Standard ambient normalized Jacquet restriction on exact finite-length K0. -/
def standardAmbientJacquetK0 (J : Finset (SimpleRoot i ν)) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  jacquetK0.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2

/-- Induce inside the target coarse Levi after actual fine-Levi conjugation
and ambient standard Jacquet restriction. -/
def standardConjugatedJacquetTerm
    (J : Finset (SimpleRoot i ν)) (I : Finset J)
    (H : Finset (SimpleRoot i ν)) (g : RationalPoint k G.X)
    (hFine : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J I) ↔ g⁻¹ * x * g ∈ levi i ν H) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl J I).comp
    ((conjugationK0.{u, max (u + 1) v} g hFine).comp
      (standardAmbientJacquetK0.{u, v} i ν hG hi hν hStandard hU hfl H))

variable (Js Jt : Finset (SimpleRoot i ν)) (Is : Finset Js) (It : Finset Jt)
  (g : RationalPoint k G.X)
  (hCoarse : ∀ x : RationalPoint k G.X,
    x ∈ levi i ν Jt ↔ g⁻¹ * x * g ∈ levi i ν Js)
  (hFine : ∀ x : RationalPoint k G.X,
    x ∈ levi i ν (leviIndex Jt It) ↔
      g⁻¹ * x * g ∈ levi i ν (leviIndex Js Is))
  (hParabolic : ∀ x : levi i ν Jt,
    (x : RationalPoint k G.X) ∈ parabolic i ν (leviIndex Jt It) ↔
      g⁻¹ * (x : RationalPoint k G.X) * g ∈ parabolic i ν (leviIndex Js Is))
  (hRadical : ∀ x : levi i ν Jt,
    (x : RationalPoint k G.X) ∈ unipotent i ν (leviIndex Jt It) ↔
      g⁻¹ * (x : RationalPoint k G.X) * g ∈ unipotent i ν (leviIndex Js Is))
  (hWc : Jacquet.Localization.IsLimitOfCompactSubgroups
    ((unipotent i ν (leviIndex Js Is)).subgroupOf (levi i ν Js)))
  (hδ :
    (HaarModulus.closedRestrictCharacter (unipotent i ν Js) (hU Js) (levi i ν Js)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν Js).levi_le_normalizer).comp
        (Subgroup.inclusion
          (levi_le_of_subset i ν hInter hG hi hν _ Js (leviIndex_subset Js Is))) *
      standardInnerJacquetModulus i ν hInter hG hi hν hU Js Is (hM Js) =
    HaarModulus.closedRestrictCharacter (unipotent i ν (leviIndex Js Is))
      (hU (leviIndex Js Is)) (levi i ν (leviIndex Js Is))
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex Js Is)).levi_le_normalizer)

include hParabolic hRadical in
/-- The actual rational fine-induction conjugation square. -/
theorem standardLeviInductionK0_transport :
    (conjugationK0.{u, max (u + 1) v} g hCoarse).comp
        (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl Js Is) =
      (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl Jt It).comp
        (conjugationK0.{u, max (u + 1) v} g hFine) := by
  exact LeviConjugation.inductionMap_transport.{u, max (u + 1) v}
    (hM Js) (hM Jt)
    (levi_le_of_subset i ν hInter hG hi hν _ Js (leviIndex_subset Js Is))
    (levi_le_of_subset i ν hInter hG hi hν _ Jt (leviIndex_subset Jt It))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν Js Is)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν Jt It)
    (hU (leviIndex Js Is)) (hU (leviIndex Jt It))
    g hCoarse hFine hParabolic hRadical (hLfl Js Is) (hLfl Jt It)

include hWc hδ in
/-- The actual rational Jacquet stages square in the ambient fine-Levi model. -/
theorem standardLeviJacquetK0_comp_ambient :
    (standardLeviJacquetK0.{u, v} i ν hInter hG hi hν hU hM hLfl Js Is).comp
        (standardAmbientJacquetK0.{u, v} i ν hG hi hν hStandard hU hfl Js) =
      standardAmbientJacquetK0.{u, v}
        i ν hG hi hν hStandard hU hfl (leviIndex Js Is) := by
  unfold standardLeviJacquetK0 LeviConjugation.jacquetMap
  rw [LinearMap.comp_assoc]
  exact standardJacquetK0_stages_of_modulus.{u, v}
    i ν hInter hG hi hν hStandard hU Js Is (hM Js) hWc hδ
    (fun A => (hfl A).2.2.1) (fun A => (hfl A).2.2.2)
    (hLfl Js Is).2.2.1 (hLfl Js Is).2.2.2

/-- Canonical subgroup-copy transports cancel in the actual rational inner term. -/
theorem standardLeviInductionK0_comp_jacquet :
    letI := (hM Js).locallyCompactSpace
    (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl Js Is).comp
        (standardLeviJacquetK0.{u, v} i ν hInter hG hi hν hU hM hLfl Js Is) =
      alternatingTerm.{u, u, max (u + 1) v}
        (fun K : Finset Js => (parabolic i ν (leviIndex Js K)).subgroupOf (levi i ν Js))
        (fun K : Finset Js => (levi i ν (leviIndex Js K)).subgroupOf (levi i ν Js))
        (fun K : Finset Js => (unipotent i ν (leviIndex Js K)).subgroupOf (levi i ν Js))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν Js)
        (fun K => (hU (leviIndex Js K)).preimage continuous_subtype_val)
        (hLfl Js) Is := by
  exact LeviConjugation.inductionMap_comp_jacquetMap.{u, max (u + 1) v}
    (hM Js)
    (levi_le_of_subset i ν hInter hG hi hν _ Js (leviIndex_subset Js Is))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν Js Is)
    (hU (leviIndex Js Is)) (hLfl Js Is)

include hParabolic hRadical hWc hδ in
/-- The actual conjugated standard term is the literal transported
restricted-Levi term. Subgroup geometry and positive Haar factorization
remain explicit, rather than a representation or K0 comparison premise. -/
theorem standardConjugatedJacquetTerm_eq_transported :
    standardConjugatedJacquetTerm.{u, v}
        i ν hInter hG hi hν hStandard hU hM hfl hLfl
        Jt It (leviIndex Js Is) g hFine =
      transportedLeviJacquetTerm.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) hU hfl hM Jt Js g hCoarse
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν Js)
        (hLfl Js) Is := by
  exact conjugatedStages
    (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl Js Is)
    (standardLeviInductionK0.{u, v} i ν hInter hG hi hν hU hM hLfl Jt It)
    (standardLeviJacquetK0.{u, v} i ν hInter hG hi hν hU hM hLfl Js Is)
    (standardAmbientJacquetK0.{u, v} i ν hG hi hν hStandard hU hfl Js)
    (standardAmbientJacquetK0.{u, v} i ν hG hi hν hStandard hU hfl (leviIndex Js Is))
    (conjugationK0.{u, max (u + 1) v} g hCoarse)
    (conjugationK0.{u, max (u + 1) v} g hFine) _
    (standardLeviInductionK0_transport.{u, v}
      i ν hInter hG hi hν hU hM hLfl Js Jt Is It g
      hCoarse hFine hParabolic hRadical)
    (standardLeviJacquetK0_comp_ambient.{u, v}
      i ν hInter hG hi hν hStandard hU hM hfl hLfl Js Is hWc hδ)
    (standardLeviInductionK0_comp_jacquet.{u, v}
      i ν hInter hG hi hν hU hM hLfl Js Is)

end Langlands.Aubert.General.RationalPointFamily
