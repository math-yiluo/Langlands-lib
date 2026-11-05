import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureReduction
import Langlands.GroupScheme.Rational.CompatibleTorusCocharacter
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProduct
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductStatement
import Langlands.GroupScheme.PseudoParabolicSplitRadicalContainmentStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Minimal pseudo-parabolics as products of a torus centralizer and a split radical

The minimality direction of the criterion in CGP Proposition C.2.4, conditional on
explicit published structural statements. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G P : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

namespace IsMinimalPseudoParabolicSubgroup

/-- A minimal pseudo-parabolic containing the dynamic parabolic of a cocharacter `ψ`
is the represented product of `P_G(ψ)` with the ground-field unipotent radical. -/
theorem isFppfProduct_parabolic
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : P ⟶ G} (hi : IsMinimalPseudoParabolicSubgroup i)
    {R : GroupScheme (Spec (CommRingCat.of k))} {r : R ⟶ G} (hr : IsUnipotentRadical r)
    (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψ : Dynamic.parabolic ψ ≤ SubgroupFunctor.range i) :
    (Dynamic.parabolic ψ).IsFppfProduct (SubgroupFunctor.range r) i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom ψ
  obtain ⟨Q, q, hq, -, -⟩ := smoothConnectedNormalFactorFppfProductExistence k G inferInstance
    inferInstance _ _ (Dynamic.Affine.parabolicHom ψ) r
    (Dynamic.Affine.isClosedSubgroup_parabolicHom ψ) ((dynamicSmooth k G ψ _ _).1 hrep)
    (DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic G ψ hrep)
    hr.isClosedSubgroup hr.smooth hr.connectedSpace hr.isNormal
  rw [hrep.2] at hq
  have hqp : IsPseudoParabolicSubgroup q :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨R, r, ψ, hr, hq⟩⟩
  have heq : SubgroupFunctor.range q = SubgroupFunctor.range i :=
    hi.range_eq_of_le hqp (hq.le_range i hψ (hi.isPseudoParabolicSubgroup.radical_le hr))
  refine ⟨hi.isClosedSubgroup, fun T x => ?_⟩
  rw [← heq]
  exact hq.mem_range_iff T x

/-- Conditionally on CGP Proposition 2.2.4 and Corollary 2.2.5 (containment): a minimal
pseudo-parabolic whose subgroup functor contains `P_G(ν)` for a cocharacter `ν` of a split
torus `s` of `P` is the represented product of `Z_G(S)` and its split ground-field radical. -/
theorem isFppfProduct_torusCentralizer_of_parabolic_le
    (h224 : PseudoParabolicSplitRadicalProductStatement.{u})
    (h225 : PseudoParabolicSplitRadicalContainmentStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : P ⟶ G} (hi : IsMinimalPseudoParabolicSubgroup i)
    {s : S.toGrp ⟶ P} (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S)
    (hν : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ s ≫ i) ≤ SubgroupFunctor.range i)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ P} (hj : IsSplitUnipotentRadical j) :
    SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
      (SubgroupFunctor.range (j ≫ i)) i := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨ζ, hZ, hP, -⟩ := hS.exists_compatible_cocharacter (s ≫ i) ν
  set ψ := CommGroupScheme.groupHom ζ ≫ s ≫ i
  have hψ : Dynamic.parabolic ψ ≤ SubgroupFunctor.range i := hP.trans hν
  obtain ⟨R, r, -, hr, -⟩ := hi.isPseudoParabolicSubgroup.presentation
  have hPi := hi.isFppfProduct_parabolic hr ψ hψ
  obtain ⟨V, n, hn⟩ := SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence k G
  obtain ⟨hUj, hnj⟩ := h225 k G R r hr ψ P i hPi V U n j hn hj
  have hZi : torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i := by
    rw [← hZ]
    exact (Dynamic.centralizer_le_parabolic ψ).trans hψ
  refine ⟨hi.isClosedSubgroup, fun T x => ⟨fun hx => ?_, fun hx =>
    hx.mem_range_of_le i hZi (SubgroupFunctor.range_comp_le j i)⟩⟩
  obtain ⟨W, w, hf, hs, hl, p, m, hp, hm, he⟩ :=
    (h224 k G R V r n hr hn ψ T x).mp ((hPi.mem_range_iff T x).mp hx)
  set z := Dynamic.limit ψ ⟨p, hp⟩
  have hz : z ∈ (Dynamic.centralizer ψ).carrier W := Dynamic.limit_mem_centralizer ψ _
  have hu : z⁻¹ * (p * z⁻¹) * z⁻¹⁻¹ ∈ (Dynamic.unipotent ψ).carrier W :=
    Dynamic.conj_mem_unipotent ψ
      ((Dynamic.parabolic ψ).carrier W |>.inv_mem (Dynamic.centralizer_le_parabolic ψ W hz))
      (Dynamic.mul_inv_limit_mem_unipotent ψ ⟨p, hp⟩)
  refine ⟨W, w, hf, hs, hl, z, z⁻¹ * (p * z⁻¹) * z⁻¹⁻¹ * m, ?_, ?_, ?_⟩
  · rw [← hZ]
    exact hz
  · exact (SubgroupFunctor.range (j ≫ i)).carrier W |>.mul_mem (hUj W hu) (hnj W hm)
  · rw [he]
    group

/-- Conditionally on conjugacy of maximal split tori (CGP Theorem C.2.3), CGP Proposition
2.2.4 and Corollary 2.2.5 (containment): a minimal pseudo-parabolic is the represented product of the
centralizer `Z_G(S)` of any of its maximal split tori and its split ground-field radical. -/
theorem isFppfProduct_torusCentralizer
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (h224 : PseudoParabolicSplitRadicalProductStatement.{u})
    (h225 : PseudoParabolicSplitRadicalContainmentStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : P ⟶ G} (hi : IsMinimalPseudoParabolicSubgroup i)
    {s : S.toGrp ⟶ P} (hs : IsMaximalSplitTorus s)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ P} (hj : IsSplitUnipotentRadical j) :
    SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
      (SubgroupFunctor.range (j ≫ i)) i := by
  have hpi := hi.isPseudoParabolicSubgroup
  obtain ⟨hPs, hPc, hPa⟩ := pseudoParabolicSubgroupStructure k G P i hpi
  have : IsClosedImmersion i.hom.hom.left := hpi.isClosedSubgroup
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  obtain ⟨χ, hχ⟩ := hpi.exists_cocharacter_le
  have hχi : SubgroupFunctor.range χ ≤ SubgroupFunctor.range i :=
    (Dynamic.range_le_parabolic χ).trans hχ
  obtain ⟨p, ξ, hpξ⟩ :=
    exists_innerIso_comp_eq_cocharacter hconj hs (hrep.factorHom χ hχi)
  have hχc : χ ≫ (G.innerIso (p ≫ i.hom.hom)).hom =
      CommGroupScheme.groupHom ξ ≫ (s ≫ i) := by
    rw [← hrep.factorHom_comp χ hχi, Category.assoc, comp_innerIso_hom_comp,
      reassoc_of% hpξ]
  have hν : Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ s ≫ i) ≤
      SubgroupFunctor.range i := by
    rw [← hχc]
    exact IsPseudoParabolicSubgroup.parabolic_comp_innerIso_le_range χ hχ p
  exact hi.isFppfProduct_torusCentralizer_of_parabolic_le h224 h225 hs.1.1 ξ hν hj

end IsMinimalPseudoParabolicSubgroup

/-- The forward implication of the minimality criterion of CGP Proposition C.2.4: a minimal
pseudo-parabolic subgroup `P` of a smooth connected affine group `G` over a field is the
fppf-local product `Z_G(S) · R_us,k(P)` for every maximal split torus `S` of `P` and every
split unipotent radical of `P`. This proposition is the conclusion of the conditional
reduction `pseudoParabolicCentralizerProductOfMinimality_of_statements`, not an assertion
that it holds unconditionally. -/
def PseudoParabolicCentralizerProductOfMinimality : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ P),
        IsMaximalSplitTorus s →
          ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ P),
            IsSplitUnipotentRadical j →
              IsMinimalPseudoParabolicSubgroup i →
                SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
                  (SubgroupFunctor.range (j ≫ i)) i

/-- Conditionally on C.2.3, Proposition 2.2.4 and Corollary 2.2.5 (containment), minimality
implies the product criterion. -/
theorem pseudoParabolicCentralizerProductOfMinimality_of_statements
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (h224 : PseudoParabolicSplitRadicalProductStatement.{u})
    (h225 : PseudoParabolicSplitRadicalContainmentStatement.{u}) :
    PseudoParabolicCentralizerProductOfMinimality.{u} := by
  intro k _ G P _ _ _ i _ S s hs U j hj hmin
  exact hmin.isFppfProduct_torusCentralizer hconj h224 h225 hs hj

end Langlands.GroupScheme
