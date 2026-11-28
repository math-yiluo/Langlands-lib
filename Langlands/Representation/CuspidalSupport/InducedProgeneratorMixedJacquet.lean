import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.Representation.Category.DisjointConstituentCoproduct
import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndFreeReduction
import Langlands.Representation.CuspidalSupport.RationalSummandInductionMembership
import Langlands.Representation.Exponents.ArbitraryParabolicTemperedAmbientTransport
import Langlands.Representation.Filtration.ProjectiveGradeProjection
import Langlands.Representation.Geometric.MaximalLeviOppositeNormalizer

/-! # The inertial projection of a mixed Jacquet module for a maximal Levi -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme CuspidalSupport Plancherel

section Pullback

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

local instance mixedJacquetLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology k M.X
local instance mixedJacquetLeviTopologicalGroup : IsTopologicalGroup (rationalPoints M) :=
  rationalPoint_isTopologicalGroup k M

private theorem pullback_summand_mem_block
    (hM : IsConnectedReductive M) (e : rationalPoints M ≃ₜ* rationalPoints M)
    (he : ∀ x, e x ∈ rationalCommonNormKernel M ↔ x ∈ rationalCommonNormKernel M)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (hπ : π.IsIrreducible)
    (ρ₀ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel M)) (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel M) π)
    (hj : Function.Injective (SmoothRep.hom j)) :
    rationalInertiaBlockProperty M (rationalInertiaBaseLift M (SmoothRep.pullback e π))
      (SmoothRep.pullback e (rationalNormKernelSummandInduction M ρ₀)) := by
  let H := rationalCommonNormKernel M
  let eH := QuotientIntegration.subgroupAutomorphism H e he
  let πe := SmoothRep.pullback e π
  let ρe := SmoothRep.pullback eH ρ₀
  let je : ρe ⟶ SmoothRep.restrictSubgroup H πe := SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom j).toLinearMap
      isIntertwining' := fun h => (SmoothRep.hom j).isIntertwining' (eH h) }
  have hπe : πe.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.representation e).mpr hπ
  have hρe : ρe.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff ρ₀.representation eH).mpr hρ₀
  exact rationalInertiaBlockProperty_of_iso
    (rationalSummandInduction_mem_block M hM πe hπe ρe hρe je hj)
    (compactInductionPullbackIso H e he (SmoothRep.toRep.obj ρ₀))

end Pullback

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N Q U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance mixedJacquetAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 1000000 in
/-- In the absence of an inertia-preserving normalizer outside the Levi, the mixed Jacquet
module of the norm-kernel summand induction projects onto the identity grade. This is a
split projection and precomposition with it is bijective on maps to the inertia block. -/
def mixedJacquetInertialProjection
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (hlevi : lQ ≫ q = l ≫ p)
    (hinf : SubgroupFunctor.range p ⊓ SubgroupFunctor.range q = SubgroupFunctor.range (l ≫ p))
    (hproper : ¬ IsIso p)
    (hmax : ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (j : R ⟶ G) (f : P ⟶ R),
      IsParabolicSubgroup j → f ≫ j = p → IsIso f ∨ IsIso j)
    (hne : SubgroupFunctor.range p ≠ SubgroupFunctor.range q) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints M)), π.IsIrreducible → IsSupercuspidal π →
    ∀ (ρ₀ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel M)), ρ₀.IsIrreducible →
    ∀ (j : ρ₀ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel M) π),
      Function.Injective (SmoothRep.hom j) →
      (∀ (g : rationalPoints G) (φ : M ≅ M),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom → g ∉ pointImage (l ≫ p) →
        ¬ IsRationalInertiaRelated M (rationalInertiaBaseLift M π)
          (rationalInertiaBaseLift M (SmoothRep.pullback (ambientIsoPointsEquiv φ) π))) →
      let A := rationalNormKernelSummandInduction M ρ₀
      let B := (leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
        ((leviInductionFunctor p l r hp hr hl hmul).obj A)
      Σ a : B ⟶ A, { b : A ⟶ B // b ≫ a = 𝟙 A ∧
        ∀ X, rationalInertiaBlockProperty M (rationalInertiaBaseLift M π) X →
          Function.Bijective (fun f : A ⟶ X => a ≫ f) } := by
  classical
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ hsc ρ₀ hρ₀ j hj hNo A B
  apply Classical.choice
  have hproj : Projective A := projective_rationalNormKernelSummandInduction_of_jointSpecialCompact
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence p l hp hl π hsc ρ₀ j hj
  have hscA : IsSupercuspidal A := isSupercuspidal_rationalNormKernelSummandInduction π hsc ρ₀ j hj
  have hemb : (Iso.refl M).hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso 1).hom := by
    simpa only [Iso.refl_hom, Category.id_comp, innerIso_one_hom, Category.comp_id] using hlevi.symm
  have hconj : ∃ (g : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom := by
    refine ⟨1, Iso.refl M, ?_⟩
    simpa only [Iso.refl_hom, Category.id_comp, innerIso_one_hom, Category.comp_id] using hlevi
  obtain ⟨⟨m, c, z, φ, e, hc, hφ, he, s, hs⟩, -⟩ :=
    leviJacquetInductionSupercuspidalFiltration.{u, max u v} k G hG P M N Q M U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hconj A hscA
  let identity : {x : DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage q : Set (rationalPoints G)) //
      ∃ (w : rationalPoints G) (ψ : M ≅ M),
        DoubleCoset.mk (pointImage p) (pointImage q) w = x ∧
          ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso w).hom} :=
    ⟨DoubleCoset.mk (pointImage p) (pointImage q) 1, 1, Iso.refl M, rfl, hemb⟩
  let i₀ := c.symm identity
  have hi₀ : c i₀ = identity := c.apply_symm_apply identity
  have hc₀ : DoubleCoset.mk (pointImage p) (pointImage q) (z i₀) =
      DoubleCoset.mk (pointImage p) (pointImage q) 1 :=
    (hc i₀).trans (congrArg Subtype.val hi₀)
  have hnorm (i : Fin m) : (φ i).hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom := by
    simpa only [← Category.assoc lQ q, hlevi, Category.assoc] using hφ i
  obtain ⟨x, hx⟩ := mem_levi_of_normalizer_identity_doubleCoset hG hp hl hq hlQ
    hlevi hinf hproper hmax hne (z i₀) (φ i₀) (hnorm i₀) hc₀
  have hinner : e i₀ = inverseConjugation x⁻¹ := by
    apply ContinuousMulEquiv.ext
    intro y
    apply (leviPointsEquiv p l hp hl).injective
    apply Subtype.ext
    simp only [leviPointsEquiv_apply_coe]
    have h := congrArg (fun f : M ⟶ G => rationalPoints.map f y) (hnorm i₀)
    rw [pointMap_comp_apply (φ i₀).hom (l ≫ p), ← Category.assoc l p,
      pointMap_comp_apply (l ≫ p),
      rationalPoints_map_innerIso, ← he i₀ y, ← hx] at h
    simpa only [inverseConjugation_apply, inv_inv, map_mul, map_inv,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  let gradeIso (i : Fin m) : s.smoothGradedObject i ≅ SmoothRep.pullback (e i) A :=
    SmoothRep.mkIso (hs i).some
  have gradeProjective (i : Fin m) : Projective (s.smoothGradedObject i) := by
    have h : Projective (SmoothRep.pullback (e i) A) :=
      ((SmoothRep.pullbackEquivalence (e i)).map_projective_iff A).mpr hproj
    exact Projective.of_iso (gradeIso i).symm h
  let innerIso : SmoothRep.pullback (e i₀) A ≅ A := by
    rw [hinner]
    exact pullbackInverseConjugationIso x⁻¹ A
  let ε : s.smoothGradedObject i₀ ≅ A := gradeIso i₀ ≪≫ innerIso
  obtain ⟨a, b, hab, hbij⟩ := s.exists_splitProjection_of_projectiveGrades i₀ ε gradeProjective
  refine ⟨⟨a, b, hab, fun X hX => hbij X ?_⟩⟩
  intro i hi f
  have hz : z i ∉ pointImage (l ≫ p) := by
    intro hz
    have hcoset : DoubleCoset.mk (pointImage p) (pointImage q) 1 =
        DoubleCoset.mk (pointImage p) (pointImage q) (z i) :=
      DoubleCoset.eq.mpr ⟨z i, pointImage_comp_le p l hz, 1, Subgroup.one_mem _, by simp⟩
    exact hi (c.injective (Subtype.ext
      ((hc i).symm.trans (hcoset.symm.trans (congrArg Subtype.val hi₀).symm))))
  have hpoint : e i = ambientIsoPointsEquiv (φ i) := ContinuousMulEquiv.ext (he i)
  have hker (y : rationalPoints M) : e i y ∈ rationalCommonNormKernel M ↔
      y ∈ rationalCommonNormKernel M := by
    rw [he i y]
    exact Geometry.Building.ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff (φ i) y
  have hblock := rationalInertiaBlockProperty_of_iso
    (pullback_summand_mem_block hl.isConnectedReductive (e i) hker π hπ ρ₀ hρ₀ j hj) (gradeIso i)
  apply SmoothRep.hom_eq_zero_of_no_common_irreducibleSubquotient _ f
  intro D hD hDi hDX
  have hrelated := (hX D hD hDX).trans (hblock D hD hDi).symm
  exact hNo (z i) (φ i) (hnorm i) hz (hpoint ▸ hrelated)

end Langlands.Aubert.General.RepresentedParabolic
