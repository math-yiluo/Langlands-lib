import Langlands.Representation.Exponents.TemperedJacquetRestriction
import Mathlib.LinearAlgebra.Dimension.Basic

/-! # Linear restriction of Jacquet intertwiners at independent carrier universes -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance linearRestrictionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)

variable [IsAffineHom M.X.hom]

local instance linearRestrictionLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]

/-- The existing vanishing argument for algebraic intertwiners whose source
and target carriers can lie in different universes. -/
theorem leviJacquetIntertwiner_eq_zero_on_nonunitaryPart
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, w} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (f : ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
      σ.representation)
    {x : (jacquetFunctor p l r hp hr hl hmul).obj π}
    (hx : x ∈ nonunitaryJacquetPart p l r hp hl hr hmul ha π) :
    f x = 0 := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  have he : ∀ t : rationalPoints A.toGrp,
      leviPointsEquiv p l hp hl (rationalPoints.map a t) =
        splitComponentPointsMap (l ≫ p) a t := fun _ => Subtype.ext rfl
  have hf : ∀ t : rationalPoints A.toGrp,
      (σ.representation (rationalPoints.map a t)).comp f.toLinearMap =
        f.toLinearMap.comp
          (((jacquetFunctor p l r hp hr hl hmul).obj π).representation
            (splitComponentPointsMap (l ≫ p) a t)) := by
    intro t
    rw [← he t]
    exact (f.isIntertwining' (rationalPoints.map a t)).symm
  have hle : (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ≤
      f.toLinearMap.ker := by
    rw [nonunitaryJacquetPart_toSubmodule]
    refine iSup_le fun χ => iSup_le fun _ => iSup_le fun hχ => ?_
    intro y hy
    have hw := map_mem_generalizedWeightSpace_of_comp
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
      (splitComponentPointsMap (l ≫ p) a) (splitComponentPointsMap_mem_center (l ≫ p) ha)
      σ.representation (rationalPoints.map a) ha.isCentralSplitTorus.isCentral.map_mem_center
      ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth σ.isSmooth
      f.toLinearMap hf χ hy
    rw [tempered_generalizedWeightSpace_eq_bot hl.isConnectedReductive ha σ hσ χ hχ] at hw
    exact hw
  exact hle hx

omit [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)] in
/-- Actual precomposition with the unitary-part inclusion, as a complex-linear
map of intertwiner spaces at independent source and target carrier universes. -/
def leviUnitaryJacquetRestrictionLinearMap
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, w} ℂ (rationalPoints M)) :
    (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
      σ.representation) →ₗ[ℂ]
    ((leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.IntertwiningMap
      σ.representation) where
  toFun f := f.comp (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π))
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

/-- Spanning by the unitary and nonunitary parts makes restriction injective
for intertwiners into a tempered target. Disjointness is not required. -/
theorem leviUnitaryJacquetRestrictionLinearMap_injective
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, w} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (hspan : (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ⊔
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule = ⊤) :
    Function.Injective (leviUnitaryJacquetRestrictionLinearMap p l r hp hl hr hmul ha π σ) := by
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f (x : (jacquetFunctor p l r hp hr hl hmul).obj π) = g x
  have hx : x ∈ (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ⊔
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule := by
    rw [hspan]
    trivial
  obtain ⟨s, hs, q, hq, hsq⟩ := (Submodule.mem_sup
    (R := ℂ) (M := (jacquetFunctor p l r hp hr hl hmul).obj π)).mp hx
  rw [← hsq]
  have hsfg := congrArg (fun F => F ⟨s, hs⟩) hfg
  change f s = g s at hsfg
  let F : (jacquetFunctor p l r hp hr hl hmul).obj π →ₗ[ℂ] σ := f.toLinearMap
  let H : (jacquetFunctor p l r hp hr hl hmul).obj π →ₗ[ℂ] σ := g.toLinearMap
  have hfq : F q = 0 :=
    leviJacquetIntertwiner_eq_zero_on_nonunitaryPart p l r hp hl hr hmul ha π σ hσ f hq
  have hgq : H q = 0 :=
    leviJacquetIntertwiner_eq_zero_on_nonunitaryPart p l r hp hl hr hmul ha π σ hσ g hq
  change F s = H s at hsfg
  change F (s + q) = H (s + q)
  rw [map_add, map_add, hfq, hgq, hsfg]

/-- Any rank-at-most-one bound on the actual unitary Jacquet Hom space
therefore gives the bound on the whole Jacquet Hom space. -/
theorem leviJacquetHom_rank_le_one_of_unitaryPart
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, w} ℂ (rationalPoints M))
    (hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ)
    (hspan : (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ⊔
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule = ⊤)
    (hdim : Module.rank ℂ
      ((leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation.IntertwiningMap
        σ.representation) ≤ 1) :
    Module.rank ℂ
      (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
        σ.representation) ≤ 1 := by
  exact (LinearMap.rank_le_of_injective
    (leviUnitaryJacquetRestrictionLinearMap p l r hp hl hr hmul ha π σ)
    (leviUnitaryJacquetRestrictionLinearMap_injective p l r hp hl hr hmul ha π σ hσ hspan)).trans hdim

end Langlands.Aubert.General.RepresentedParabolic
