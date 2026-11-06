import Langlands.Representation.Exponents.TemperedGroupWeights
import Langlands.Representation.Exponents.TemperedJacquetUnitaryRestrictionStatement
import Langlands.Representation.Category.ComplementaryCoproduct

/-! # Restriction to the unitary Jacquet part -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedRestrictionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)

variable [IsAffineHom M.X.hom]

local instance temperedRestrictionLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]

/-- A Levi intertwiner into a tempered target kills every nonunitary Jacquet weight. -/
theorem leviJacquetHom_eq_zero_on_nonunitary_weight
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (f : (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0)
    {x : (jacquetFunctor p l r hp hr hl hmul).obj π}
    (hx : x ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ) :
    SmoothRep.hom f x = 0 := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  have he : ∀ t : rationalPoints A.toGrp,
      leviPointsEquiv p l hp hl (rationalPoints.map a t) =
        splitComponentPointsMap (l ≫ p) a t := fun _ => Subtype.ext rfl
  have hf : ∀ t : rationalPoints A.toGrp,
      (σ.representation (rationalPoints.map a t)).comp (SmoothRep.hom f).toLinearMap =
        (SmoothRep.hom f).toLinearMap.comp
          (((jacquetFunctor p l r hp hr hl hmul).obj π).representation
            (splitComponentPointsMap (l ≫ p) a t)) := by
    intro t
    rw [← he t]
    exact ((SmoothRep.hom f).isIntertwining' (rationalPoints.map a t)).symm
  have hw := map_mem_generalizedWeightSpace_of_comp
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
    (splitComponentPointsMap (l ≫ p) a) (splitComponentPointsMap_mem_center (l ≫ p) ha)
    σ.representation (rationalPoints.map a) ha.isCentralSplitTorus.isCentral.map_mem_center
    ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth σ.isSmooth
    (SmoothRep.hom f).toLinearMap hf χ hx
  rw [tempered_generalizedWeightSpace_eq_bot hl.isConnectedReductive ha σ hσ χ hχ] at hw
  exact hw

/-- Every map from a Jacquet module into a tempered Levi representation vanishes
on the whole nonunitary part. No temperedness of the source is needed. -/
theorem leviJacquetHom_eq_zero_on_nonunitaryPart
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (f : (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ)
    {x : (jacquetFunctor p l r hp hr hl hmul).obj π}
    (hx : x ∈ nonunitaryJacquetPart p l r hp hl hr hmul ha π) :
    SmoothRep.hom f x = 0 := by
  have hle : (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ≤
      (SmoothRep.hom f).toLinearMap.ker := by
    rw [nonunitaryJacquetPart_toSubmodule]
    refine iSup_le fun χ => iSup_le fun _ => iSup_le fun hχ => ?_
    intro x hx
    exact leviJacquetHom_eq_zero_on_nonunitary_weight p l r hp hl hr hmul ha π σ hσ f χ hχ hx
  exact hle hx

/-- The actual unitary subspace, as an invariant subspace for the transported
Jacquet representation of the Levi itself. -/
def leviUnitaryJacquetSubrepresentation
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Subrepresentation ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation where
  toSubmodule := (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
  apply_mem_toSubmodule m :=
    (unitaryJacquetPart p l r hp hl hr hmul ha π).apply_mem_toSubmodule
      (leviPointsEquiv p l hp hl m)

/-- The actual nonunitary subspace, as an invariant subspace for the transported
Jacquet representation of the Levi itself. -/
def leviNonunitaryJacquetSubrepresentation
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Subrepresentation ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation where
  toSubmodule := (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
  apply_mem_toSubmodule m :=
    (nonunitaryJacquetPart p l r hp hl hr hmul ha π).apply_mem_toSubmodule
      (leviPointsEquiv p l hp hl m)

/-- Extension by zero along the actual complementary nonunitary Jacquet part.
Complementarity is an explicit input to this supporting construction. -/
def leviUnitaryJacquetExtendByZero
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hcompl : IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (f : leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶ σ) :
    (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ :=
  SmoothRep.complementaryDesc
    (S := leviUnitaryJacquetSubrepresentation p l r hp hl hr hmul ha π)
    (Q := leviNonunitaryJacquetSubrepresentation p l r hp hl hr hmul ha π)
    hcompl f 0

omit [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)] in
/-- The extension restricts to the prescribed map on the unitary part. -/
@[simp] theorem leviUnitaryJacquetModuleι_extendByZero
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hcompl : IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (f : leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶ σ) :
    leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫
      leviUnitaryJacquetExtendByZero p l r hp hl hr hmul ha π σ hcompl f = f := by
  exact SmoothRep.subtype_complementaryDesc_left
    (A := (leviJacquetFunctor p l r hp hr hl hmul).obj π) (B := σ)
    (S := leviUnitaryJacquetSubrepresentation p l r hp hl hr hmul ha π)
    (Q := leviNonunitaryJacquetSubrepresentation p l r hp hl hr hmul ha π)
    hcompl f 0

/-- The actual projection onto the unitary Jacquet module, along its
complementary nonunitary part. -/
def leviUnitaryJacquetRetraction
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hcompl : IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) :
    (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶
      leviUnitaryJacquetModule p l r hp hl hr hmul ha π :=
  leviUnitaryJacquetExtendByZero p l r hp hl hr hmul ha π
    (leviUnitaryJacquetModule p l r hp hl hr hmul ha π) hcompl (𝟙 _)

omit [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)] in
/-- The projection is a retraction of the literal unitary-part inclusion. -/
@[simp] theorem leviUnitaryJacquetModuleι_retraction
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hcompl : IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) :
    leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫
      leviUnitaryJacquetRetraction p l r hp hl hr hmul ha π hcompl = 𝟙 _ :=
  leviUnitaryJacquetModuleι_extendByZero p l r hp hl hr hmul ha π _ hcompl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to the actual unitary Jacquet part is an equivalence for maps
into a tempered target, provided the two Jacquet parts are complementary. -/
def leviUnitaryJacquetRestrictionEquiv
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (hcompl : IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) :
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ) ≃
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶ σ) where
  toFun f := leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f
  invFun f := leviUnitaryJacquetExtendByZero p l r hp hl hr hmul ha π σ hcompl f
  left_inv f := by
    ext x
    obtain ⟨s, q, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl hcompl x
    change LinearMap.ofIsCompl hcompl
        (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f)).toLinearMap
        0 (s.val + q.val) =
      SmoothRep.hom f (s.val + q.val)
    rw [map_add, LinearMap.ofIsCompl_apply_left hcompl s,
      LinearMap.ofIsCompl_apply_right hcompl q]
    let F : (jacquetFunctor p l r hp hr hl hmul).obj π →ₗ[ℂ] σ :=
      (SmoothRep.hom f).toLinearMap
    change F s.val + 0 = F (s.val + q.val)
    have hq : F q.val = 0 :=
      leviJacquetHom_eq_zero_on_nonunitaryPart p l r hp hl hr hmul ha π σ hσ f q.property
    rw [map_add, hq]
  right_inv f := leviUnitaryJacquetModuleι_extendByZero p l r hp hl hr hmul ha π σ hcompl f

/-- The restriction equivalence has exactly the precomposition map occurring
in the VII.2.4 target. -/
theorem leviUnitaryJacquetRestriction_bijective_of_isCompl
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (hcompl : IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) :
    Function.Bijective
      (fun f : (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ =>
        leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f) :=
  (leviUnitaryJacquetRestrictionEquiv p l r hp hl hr hmul ha π σ hσ hcompl).bijective

end Langlands.Aubert.General.RepresentedParabolic
