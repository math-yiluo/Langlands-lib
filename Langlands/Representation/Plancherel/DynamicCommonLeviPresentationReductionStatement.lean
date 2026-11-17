import Langlands.Representation.Plancherel.DynamicCommonLeviStructuralComparison
import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement

/-! # Remaining reduction from presentation-level IV.1.1 to actual common-Levi existence -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviContinuation

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviPresentationComparison DynamicCommonLeviStructuralComparison

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

/-- The precise open assembly target for supplied complete presentations realizing
both dynamic parabolics and the common Levi. The premise is IV.1.1 itself;
no convergence, rationality, squared modulus or family comparison is assumed. -/
def DynamicCommonLeviPresentationReductionStatement : Prop :=
  ConditionalParabolicIntertwiningStatement.{u, uV, uW} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (M P P' Q U U' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (p' : P' ⟶ G) (l' : M ⟶ P')
    (a : T.toGrp ⟶ M) (n : U ⟶ P) (n' : U' ⟶ P') (q : Q ⟶ G) (v : V ⟶ Q)
    (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
    (_hLevi : l ≫ p = l' ≫ p')
    (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (_hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (_hQ : (Dynamic.parabolic
      (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
    (_hv : LeviSubgroup.IsGeometricUnipotentRadical v)
    (s : Realizes χ ψ p l n) (_s' : Realizes χ ψ' p' l' n'),
    letI : Mono r.data.i.hom.hom.left :=
      r.isCompatible.maximalSplit.isSplitSubtorus.mono
    letI : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
      let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
      let := r.isCompatible.levi.isClosedSubgroup.mono
      let := r.isCompatible.parabolic.isClosedSubgroup.mono
      have : Mono (a ≫ l ≫ p).hom.hom.left := by
        change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
        infer_instance
      exact mono_of_mono_fac
        (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
    ∀ [Fintype (relativeWeylGroup r.data.i)],
      let Ppt := (SubgroupFunctor.range p).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      let P'pt := (SubgroupFunctor.range p').carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      let Mpt := parabolicLeviPointSubgroup p l
      let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      let U'pt := (SubgroupFunctor.range (n' ≫ p')).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt)
        (_hU : IsClosed (Upt : Set (rationalPoints G)))
        (h' : IsSemidirectDecomposition P'pt Mpt U'pt)
        (_hU' : IsClosed (U'pt : Set (rationalPoints G)))
        (_hP : IsClosed (Ppt : Set (rationalPoints G)))
        (_hP' : IsClosed (P'pt : Set (rationalPoints G)))
        (K : OpenSubgroup (rationalPoints G))
        (hK : IsCompact (K : Set (rationalPoints G)))
        (hPK : ∀ g : rationalPoints G, ∃ p₀ : Ppt, ∃ k : K,
          g = (p₀ : rationalPoints G) * (k : rationalPoints G))
        (hP'K : ∀ g : rationalPoints G, ∃ p₀ : P'pt, ∃ k : K,
          g = (p₀ : rationalPoints G) * (k : rationalPoints G))
        (_hr : Continuous h.projection) (_hr' : Continuous h'.projection),
        let hψK : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ, ∃ k : K,
            g = (p₀ : rationalPoints G) * (k : rationalPoints G) := by
          intro g
          obtain ⟨p₀, k, hg⟩ := hPK g
          refine ⟨subgroupHomeomorphOfEq (parabolicPoints_eq χ ψ s) p₀, k, ?_⟩
          simpa only [subgroupHomeomorphOfEq_coe] using hg
        let hψ'K : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ', ∃ k : K,
            g = (p₀ : rationalPoints G) * (k : rationalPoints G) := by
          intro g
          obtain ⟨p₀, k, hg⟩ := hP'K g
          refine ⟨subgroupHomeomorphOfEq (parabolicPoints_eq χ ψ' _s') p₀, k, ?_⟩
          simpa only [subgroupHomeomorphOfEq_coe] using hg
        ∀ (A : SmoothRep.{0, u, uV} ℂ (levi χ)),
          A.IsAdmissible → A.HasFiniteLength →
            CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A

end Langlands.Plancherel.DynamicCommonLeviContinuation
