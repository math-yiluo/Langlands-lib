import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationReductionStatement
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness

/-! # Point data for compatible actual common-Levi presentations -/

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

private theorem continuous_projection_of_eq
    {H : Type u} [Group H] [TopologicalSpace H]
    {P M U P' M' U' : Subgroup H}
    (eP : P = P') (eM : M = M') (eU : U = U')
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U')
    (hr' : Continuous h'.projection) :
    Continuous h.projection := by
  subst P'
  subst M'
  subst U'
  exact hr'

/-- The exact source point data of the presentation reduction, together
with an enumeration of its finite relative Weyl group. Both decompositions
use the same literal point Levi. -/
structure PresentationPointData
    (W : Type uW) {H : Type u} [Group H] [TopologicalSpace H]
    (P M U P' U' : Subgroup H) (K : OpenSubgroup H) where
  weyl : Fintype W
  decomposition : IsSemidirectDecomposition P M U
  radical_closed : IsClosed (U : Set H)
  decomposition' : IsSemidirectDecomposition P' M U'
  radical_closed' : IsClosed (U' : Set H)
  parabolic_closed : IsClosed (P : Set H)
  parabolic_closed' : IsClosed (P' : Set H)
  factorization : ∀ g : H, ∃ p : P, ∃ k : K, g = (p : H) * (k : H)
  factorization' : ∀ g : H, ∃ p : P', ∃ k : K, g = (p : H) * (k : H)
  projection_continuous : Continuous decomposition.projection
  projection_continuous' : Continuous decomposition'.projection

/-- Construct all required point data from compatible all-test realizations
and the original dynamic factorizations, retaining the original compact group. -/
def presentationPointData
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (M P P' U U' : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine M.X.left]
    (p : P ⟶ G) (l : M ⟶ P) (p' : P' ⟶ G) (l' : M ⟶ P')
    (a : T.toGrp ⟶ M) (n : U ⟶ P) (n' : U' ⟶ P')
    (r : ParabolicRootPresentation p l a)
    (s : Realizes χ ψ p l n) (s' : Realizes χ ψ' p' l' n')
    (K : OpenSubgroup (rationalPoints G))
    (hψK : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ, ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G))
    (hψ'K : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ', ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G)) :
    PresentationPointData (relativeWeylGroup r.data.i)
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
      (parabolicLeviPointSubgroup p l)
      ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
      ((SubgroupFunctor.range p').carrier (Over.mk (𝟙 _)))
      ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))) K := by
  let Ppt := (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))
  let P'pt := (SubgroupFunctor.range p').carrier (Over.mk (𝟙 _))
  let Mpt := parabolicLeviPointSubgroup p l
  let Upt := (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))
  let U'pt := (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))
  have eP : Ppt = parabolic ψ := parabolicPoints_eq χ ψ s
  have eP' : P'pt = parabolic ψ' := parabolicPoints_eq χ ψ' s'
  have eM : Mpt = levi χ := leviPoints_eq χ ψ s
  have eU : Upt = radical ψ := radicalPoints_eq χ ψ s
  have eU' : U'pt = radical ψ' := radicalPoints_eq χ ψ' s'
  have h : IsSemidirectDecomposition Ppt Mpt Upt := by
    rw [eP, eM, eU]
    exact commonDecomposition χ ψ hψ
  have h' : IsSemidirectDecomposition P'pt Mpt U'pt := by
    rw [eP', eM, eU']
    exact commonDecomposition χ ψ' hψ'
  have hU : IsClosed (Upt : Set (rationalPoints G)) := by
    rw [eU]
    exact radical_isClosed ψ
  have hU' : IsClosed (U'pt : Set (rationalPoints G)) := by
    rw [eU']
    exact radical_isClosed ψ'
  have hP : IsClosed (Ppt : Set (rationalPoints G)) := by
    rw [eP]
    exact DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
  have hP' : IsClosed (P'pt : Set (rationalPoints G)) := by
    rw [eP']
    exact DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
  have hr : Continuous h.projection :=
    continuous_projection_of_eq eP eM eU h (commonDecomposition χ ψ hψ)
      (commonProjection_continuous χ ψ hψ)
  have hr' : Continuous h'.projection :=
    continuous_projection_of_eq eP' eM eU' h' (commonDecomposition χ ψ' hψ')
      (commonProjection_continuous χ ψ' hψ')
  have hPK : ∀ g : rationalPoints G, ∃ p₀ : Ppt, ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G) := by
    intro g
    obtain ⟨p₀, k, hg⟩ := hψK g
    refine ⟨subgroupHomeomorphOfEq eP.symm p₀, k, ?_⟩
    simpa only [subgroupHomeomorphOfEq_coe] using hg
  have hP'K : ∀ g : rationalPoints G, ∃ p₀ : P'pt, ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G) := by
    intro g
    obtain ⟨p₀, k, hg⟩ := hψ'K g
    refine ⟨subgroupHomeomorphOfEq eP'.symm p₀, k, ?_⟩
    simpa only [subgroupHomeomorphOfEq_coe] using hg
  let : Finite (relativeWeylGroup r.data.i) :=
    hG.finite_relativeWeylGroup r.data.i r.isCompatible.maximalSplit
  exact
    { weyl := Fintype.ofFinite _
      decomposition := h
      radical_closed := hU
      decomposition' := h'
      radical_closed' := hU'
      parabolic_closed := hP
      parabolic_closed' := hP'
      factorization := hPK
      factorization' := hP'K
      projection_continuous := hr
      projection_continuous' := hr' }

/-- All point hypotheses of the presentation reduction follow from all-test
realization, the reductive structure and the originally supplied factorizations.
The two remaining proposition premises are explicit. -/
theorem commonLeviContinuationExists_of_presentations
    (hReduction : DynamicCommonLeviPresentationReductionStatement.{u, uV, uW})
    (hIV : ConditionalParabolicIntertwiningStatement.{u, uV, uW})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
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
    (hLevi : l ≫ p = l' ≫ p')
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (hQ : (Dynamic.parabolic
      (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
    (hv : LeviSubgroup.IsGeometricUnipotentRadical v)
    (s : Realizes χ ψ p l n) (s' : Realizes χ ψ' p' l' n')
    (K : OpenSubgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hψK : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ, ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G))
    (hψ'K : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ', ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (hA : A.IsAdmissible) (hAlen : A.HasFiniteLength) :
    CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A := by
  let d := presentationPointData F G hG χ ψ ψ' hψ hψ' T M P P' U U'
    p l p' l' a n n' r s s' K hψK hψ'K
  let : Fintype (relativeWeylGroup r.data.i) := d.weyl
  exact hReduction hIV F G hG χ ψ ψ' hψ hψ' T M P P' Q U U' V
    p l p' l' a n n' q v r r' hLevi hn hn' hQ hv s s'
    d.decomposition d.radical_closed d.decomposition' d.radical_closed'
    d.parabolic_closed d.parabolic_closed' K hK d.factorization d.factorization'
    d.projection_continuous d.projection_continuous' A hA hAlen

end Langlands.Plancherel.DynamicCommonLeviContinuation
