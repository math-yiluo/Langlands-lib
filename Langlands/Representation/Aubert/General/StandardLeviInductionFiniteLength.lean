import Langlands.Representation.Aubert.General.OrdinaryStagesInflation

/-! Inside-Levi finite-length preservation from ambient induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open scoped MonoidAlgebra

namespace Langlands.Aubert.General

universe uG uV

section Ordinary

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (hL : IsSemidirectDecomposition
    (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
  (hP : P₀ ≤ P₁) (hM : M₀ ≤ M₁) (hU : U₁ ≤ U₀)
  (hU₀ : IsClosed (U₀ : Set G)) (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (hproj : Continuous h₁.projection)
  (hiFl : SmoothRep.PreservesFiniteLength
    (normalizedInductionFunctor.{uG, uV} h₀ hU₀))

include h₀ h₁ hP hM hU hU₀ hδ₀ hproj hiFl in
/-- Ambient fine induction of finite-length coefficients implies finite length
of their actual ordinary induction inside the coarser Levi. -/
theorem isFiniteLength_ordinaryInduction_in_levi
    (A : SmoothRep.{0, uG, uV} ℂ (M₀.subgroupOf M₁))
    (hA : A.HasFiniteLength) :
    IsFiniteLength ℂ[M₁]
      (Induction.smoothInduced (P₀.subgroupOf M₁)
        (A.representation.comp hL.projection)).asModule := by
  let e := subgroupOfContinuousEquiv hM
  let B := SmoothRep.pullback e.symm A
  have hB : B.HasFiniteLength :=
    SmoothRep.pullbackFunctor_preservesFiniteLength e.symm A hA
  have hFine := isFiniteLength_ordinaryInduction h₀ hU₀ hδ₀ hiFl B hB
  have hOuter := FiniteLengthAssembly.finiteLength_of_surjective
    (ordinaryStagesInflationEquiv h₀ h₁ hL hP hM hU hproj B).toIntertwiningMap
    (ordinaryStagesInflationEquiv h₀ h₁ hL hP hM hU hproj B).toLinearEquiv.surjective
    hFine
  have hInfSmooth := isSmooth_comp h₁.projection hproj
    (Induction.smoothInduced_smooth (P₀.subgroupOf M₁)
      ((B.representation.comp e.toMonoidHom).comp hL.projection))
  have hInf := Induction.isFiniteLength_of_smoothInduced P₁ _ hInfSmooth hOuter
  have hSurj : Function.Surjective h₁.projection := by
    intro m
    exact ⟨⟨m, h₁.levi_le m.property⟩, h₁.projection_levi m⟩
  have hInside := (FiniteLengthAssembly.finiteLength_comp_surjective_iff
    (Induction.smoothInduced (P₀.subgroupOf M₁)
      ((B.representation.comp e.toMonoidHom).comp hL.projection))
    h₁.projection hSurj).mpr hInf
  have he : B.representation.comp e.toMonoidHom = A.representation := by
    ext m v
    change A.representation (e.symm (e m)) v = A.representation m v
    rw [e.symm_apply_apply]
  change IsFiniteLength ℂ[M₁]
    (Induction.smoothInduced (P₀.subgroupOf M₁)
      ((B.representation.comp e.toMonoidHom).comp hL.projection)).asModule at hInside
  rw [he] at hInside
  exact hInside

variable [LocallyCompactSpace M₁]
  (hUL : IsClosed ((U₀.subgroupOf M₁) : Set M₁))
  (hδL : IsUnimodularModulus (U₀.subgroupOf M₁) hUL)

include h₀ h₁ hP hM hU hU₀ hδ₀ hproj hiFl hδL in
/-- The half-character on the inside Levi may be absorbed into the finite-length
coefficient representation, so ordinary preservation gives actual normalized
preservation. -/
theorem normalizedInduction_in_levi_preservesFiniteLength :
    SmoothRep.PreservesFiniteLength
      (normalizedInductionFunctor.{uG, uV} hL hUL) := by
  intro A hA
  let χ := HaarModulus.closedHalfCharacter (U₀.subgroupOf M₁) hUL
    (M₀.subgroupOf M₁) hL.levi_le_normalizer
  have hχ := HaarModulus.isOpen_ker_closedHalfCharacter (U₀.subgroupOf M₁) hUL
    (M₀.subgroupOf M₁) hL.levi_le_normalizer
  let C := A.twist χ hχ
  have hC : C.HasFiniteLength := (finiteLength_twist_iff χ A.representation).mpr hA
  have hOrd := isFiniteLength_ordinaryInduction_in_levi
    h₀ h₁ hL hP hM hU hU₀ hδ₀ hproj hiFl C hC
  have he : inducingRepresentation hL hUL A = C.representation.comp hL.projection := by
    ext p v
    change (HaarModulus.closedHalfCharacter (U₀.subgroupOf M₁) hUL
        (P₀.subgroupOf M₁) hL.le_normalizer p : ℂ) •
        A.representation (hL.projection p) v =
      (χ (hL.projection p) : ℂ) • A.representation (hL.projection p) v
    rw [closedHalfCharacter_eq_comp_projection hL hUL hδL]
    rfl
  change IsFiniteLength ℂ[M₁]
    (Induction.smoothInduced (P₀.subgroupOf M₁) (inducingRepresentation hL hUL A)).asModule
  rw [he]
  exact hOrd

end Ordinary

end Langlands.Aubert.General

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalLeviInductionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Ambient normalized-induction finite length implies finite-length
preservation for actual normalized induction inside each closed standard
Levi, with no normalized-induction-in-stages premise. -/
theorem standardLeviInduction_preservesFiniteLength
    (hStandard : StandardCocharacterStatement.{u})
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hproj : ∀ I, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
    (hiFl : ∀ I, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)))
    (J : Finset (SimpleRoot i ν))
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X))) :
    letI := hM.locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)) := by
  let _ := hM.locallyCompactSpace
  intro I
  exact normalizedInduction_in_levi_preservesFiniteLength
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (leviIndex J I))
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (parabolic_le_of_subset i ν hInter hG hi hν hStandard
      _ J (leviIndex_subset J I))
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (unipotent_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (hU (leviIndex J I))
    (isUnimodularModulus_of_isLimitOfCompactSubgroups _ (hU (leviIndex J I))
      (hUc (leviIndex J I)))
    (hproj J) (hiFl (leviIndex J I))
    ((hU (leviIndex J I)).preimage continuous_subtype_val)
    (isUnimodularModulus_of_isLimitOfCompactSubgroups _
      ((hU (leviIndex J I)).preimage continuous_subtype_val)
      (standardLeviUnipotent_isLimitOfCompactSubgroups i ν hUc J hM I))

end Langlands.Aubert.General.RationalPointFamily
