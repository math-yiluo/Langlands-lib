import Langlands.Representation.Plancherel.CompactIntertwiningUniformNumerator
import Langlands.Representation.Plancherel.CompactIntertwiningWeakRegularity
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.Representation.Plancherel.RationalUnramifiedLocalDivisibilityProof

/-! # The uniform regular numerator for actual rational-point parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

section DynamicBasis

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsSeparated G.X.hom]

local instance dynamicBasisAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance dynamicBasisTopology : TopologicalSpace (RationalPoint k G.X) :=
  rationalPointTopology k G.X

/-- For every cocharacter, the rational points of its dynamic radical, its
centralizer and the opposite dynamic radical admit an opposite Iwahori
contraction basis for one point of the centralizer. -/
theorem exists_dynamic_oppositeIwahoriContractionBasis
    [LocallyCompactSpace (RationalPoint k G.X)] [NonarchimedeanGroup (RationalPoint k G.X)]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ g : RationalPoint k G.X, g ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) ∧
      Jacquet.HasOppositeIwahoriContractionBasis
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g := by
  have : T2Space k := Langlands.BruhatTits.localField_t2Space k
  have hOc : IsClosed (((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier
      (Over.mk (𝟙 _)) : Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) :=
    isClosed_rationalPoint_subgroup k _ (Dynamic.Affine.unipotentHom _)
      (Dynamic.Affine.isRepresentedBy_unipotentHom _)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom _)
  have hUc : IsClosed (((Dynamic.unipotent χ).carrier
      (Over.mk (𝟙 _)) : Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) :=
    isClosed_rationalPoint_subgroup k _ (Dynamic.Affine.unipotentHom _)
      (Dynamic.Affine.isRepresentedBy_unipotentHom _)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom _)
  obtain ⟨g, hgM, hcomm, hcontrU, hcontrO⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint (F := k) χ
  refine ⟨g, hgM, ?_⟩
  have htop : (rationalPointTopology k G.X) = rationalSchemeTopology k G.X :=
    rationalPointTopology_eq_rationalSchemeTopology k G.X
  refine Jacquet.hasOppositeIwahoriContractionBasis_of_contraction hOc hUc hgM hcomm ?_ ?_
    (Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique χ) ?_
    hcontrU hcontrO
  · rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · have hcell := Dynamic.opposite_cell_mem_nhds_one k G χ
    rw [← htop] at hcell
    exact hcell

end DynamicBasis

section Presentation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance presentationAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance presentationTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The rational points of the opposite dynamic radical of the split-component
cocharacter of a parabolic root presentation. -/
def parabolicOppositeRadicalPoints : Subgroup (rationalPoints G) :=
  (Dynamic.unipotent (Dynamic.inverseCocharacter
    (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))).carrier (Over.mk (𝟙 _))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The literal Levi point subgroup normalizes the opposite radical points. -/
theorem parabolicLevi_le_normalizer_oppositeRadicalPoints :
    parabolicLeviPointSubgroup p l ≤
      Subgroup.normalizer (parabolicOppositeRadicalPoints r : Set (rationalPoints G)) := by
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  have hM : parabolicLeviPointSubgroup p l = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    change (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) = _
    rw [r.levi_eq_splitComponentCocharacter]
  rw [hM, ← Dynamic.centralizer_inverseCocharacter χ]
  exact Dynamic.centralizer_le_normalizer_unipotent _ _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The opposite radical points meet the actual parabolic points trivially. -/
theorem eq_one_of_mem_parabolic_of_mem_oppositeRadicalPoints {x : rationalPoints G}
    (hxP : x ∈ (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (hxU : x ∈ parabolicOppositeRadicalPoints r) : x = 1 := by
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  have hP : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) =
      (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
    rw [r.parabolic_eq_splitComponentCocharacter]
  rw [hP] at hxP
  exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hxU hxP

/-- For any supplied geometric radical, the actual radical points, the literal
Levi points and the opposite radical points carry an opposite Iwahori
contraction basis for one point. -/
theorem parabolicLevi_exists_oppositeBasis [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    {U : GroupScheme (Spec (CommRingCat.of F))} {n : U ⟶ P}
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    ∃ g : rationalPoints G, Jacquet.HasOppositeIwahoriContractionBasis
      ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
      (parabolicLeviPointSubgroup p l) (parabolicOppositeRadicalPoints r) g := by
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  obtain ⟨g, _hgM, hg⟩ := exists_dynamic_oppositeIwahoriContractionBasis (k := F) (G := G) χ
  have hU : (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)) =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [r.range_comp_radical_eq hn]
  have hM : parabolicLeviPointSubgroup p l = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    change (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) = _
    rw [r.levi_eq_splitComponentCocharacter]
  refine ⟨g, ?_⟩
  rw [hU, hM]
  exact hg

end Presentation

section Host

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' U U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {p' : P' ⟶ G} {l' : M ⟶ P'} (r' : ParabolicRootPresentation p' l' a)
  (hLevi : l ≫ p = l' ≫ p')
  {n : U ⟶ P} {n' : U' ⟶ P'} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')

local instance hostAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance hostTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance hostLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

variable [Smooth G.X.hom] [IsSeparated G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt P'pt U'pt : Subgroup (rationalPoints G)}
  (hPpt : Ppt = (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
  (hU'pt : U'pt = (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
  (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
  (hU : IsClosed (Upt : Set (rationalPoints G))) (hδ : IsUnimodularModulus Upt hU)
  (K : OpenSubgroup (rationalPoints G)) (hP : IsClosed (Ppt : Set (rationalPoints G)))
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hr : Continuous h.projection)
  (h' : IsSemidirectDecomposition P'pt (parabolicLeviPointSubgroup p l) U'pt)
  (hU' : IsClosed (U'pt : Set (rationalPoints G))) (hδ' : IsUnimodularModulus U'pt hU')
  (hP' : IsClosed (P'pt : Set (rationalPoints G)))
  (hP'K : ∀ g : rationalPoints G, ∃ p : P'pt, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace U'pt] [BorelSpace U'pt]
  [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
  [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
  [BorelSpace (QuotientSpace (U := Upt) U'pt)]
  (qν : Measure (QuotientSpace (U := Upt) U'pt))
  (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
  (hsq : SquaredModulusCompatibility h hU h' hU')

omit [LocallyOfFiniteType M.X.hom] in
include r r' hLevi hn hn' hPpt hUpt hU'pt in
/-- **Uniform regular numerator for actual rational-point parabolics.** For an
admissible finite-length representation of the literal Levi point subgroup and
any set of parameters at which the actual standard integral converges on the
whole source, one nonzero regular scalar `b` makes `b` times the actual
compact standard operator a polynomial operator family. -/
theorem parabolicLevi_exists_uniform_standardCompactOperator_numerator
    (π : Langlands.SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hadm : π.IsAdmissible) (hfin : π.HasFiniteLength)
    (Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)))
    (hfull : ∀ χ : Ω, domain h hU U'pt
      (π.twist χ.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ.val)) qν = ⊤) :
    ∃ b : unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r), b ≠ 0 ∧
      IsPolynomialOperatorOn Ω (fun χ : Ω => b.val χ.val •
        standardCompactOperator h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
          (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
          qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq χ.val π (hfull χ)) := by
  have h1 := parabolicLevi_exists_oppositeBasis r hn
  obtain ⟨g, hbasis⟩ := h1
  have h2 := parabolicLevi_exists_oppositeBasis (F := F) (G := G)
    (P := P') (p := p') (l := l') (a := a) r' (U := U') (n := n') hn'
  obtain ⟨a', htarget⟩ := h2
  have hM' : parabolicLeviPointSubgroup p' l' = parabolicLeviPointSubgroup p l :=
    congrArg (fun f : M ⟶ G =>
      (SubgroupFunctor.range f).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hLevi.symm
  rw [hM', ← hU'pt] at htarget
  rw [← hUpt] at hbasis
  have hPUbar' : ∀ x : rationalPoints G, x ∈ Ppt → x ∈ parabolicOppositeRadicalPoints r → x = 1 := by
    intro x hxP hxU
    rw [hPpt] at hxP
    exact eq_one_of_mem_parabolic_of_mem_oppositeRadicalPoints r hxP hxU
  have : LocallyCompactSpace U'pt := hU'.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have key := exists_uniform_standardCompactOperator_numerator h hU hδ K hP hK hPK
    (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r) hr
    π h' hU' hδ' hP' hP'K hr' qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq
    (parabolicLevi_le_normalizer_oppositeRadicalPoints r) hPUbar' g hbasis a' htarget hadm hfin Ω
    hfull
  exact key

include r r' hLevi hn hn' hPpt hUpt hU'pt in
/-- Compact rationality of the actual standard operator on an open parameter
set of full convergence, from local integrable domination alone. The numerator
is the uniform regular numerator above, and local divisibility is the
published `rationalUnramifiedLocalHypersurfaceDivisibility`. -/
theorem parabolicLevi_standardCompactRationalOn_of_dominated_of_finiteLength
    (π : Langlands.SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hadm : π.IsAdmissible) (hfin : π.HasFiniteLength)
    {Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))}
    (hΩ : IsOpen Ω)
    (hfull : ∀ χ : Ω, domain h hU U'pt
      (π.twist χ.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ.val)) qν = ⊤)
    (hdom : CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK
      (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
      hr π U'pt qν Ω) :
    StandardCompactRationalOn h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
      (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
      qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq Ω π hfull := by
  have key := parabolicLevi_exists_uniform_standardCompactOperator_numerator r r' hLevi hn hn'
    hPpt hUpt hU'pt h hU hδ K hP hK hPK hr h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hsq
    π hadm hfin Ω hfull
  obtain ⟨b, hb, hpoly⟩ := key
  exact parabolicLevi_standardCompactRationalOn_of_dominated r
    rationalUnramifiedLocalHypersurfaceDivisibility h hU hδ K hP hK hPK hr h' hU' hδ' hP' hP'K
    hr' qν μU' μI hqν hsq π hΩ hfull hdom b hb hpoly

end Host

end Langlands.Plancherel
