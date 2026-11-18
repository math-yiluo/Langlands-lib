import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetBridge
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.NormalizerPointsInfiniteFieldProof
import Langlands.LocalField.ValuativeInfinite
import Langlands.Representation.Aubert.General.InductionCentralCharacter
import Langlands.Representation.Filtration.ScalarGradedOccurrences
import Langlands.Representation.Geometric.DegenerateJacquetPieces
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # The center on the normalized Jacquet modules of the minimal principal series -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.Aubert.General
open Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.HarishChandraSchwartz

private theorem pow_sub_one_eq_zero_of_filtration {H : Type u} [Monoid H]
    {C : Type v} [Category.{w} C] {A : C ⥤ Rep.{u} ℂ H} {n : ℕ}
    (s : RepFunctorFiltration A n) (X : C) (g : H)
    {piece : Fin n → Rep.{u} ℂ H} (e : ∀ j, (s.graded j).obj X ≅ piece j)
    (h : ∀ (j : Fin n) (x : piece j), (piece j).ρ g x = x) :
    ((A.obj X).ρ g - 1) ^ n = 0 := by
  have lower (j : Fin n) (x : A.obj X) (hx : x ∈ (s.step j.succ).obj X) :
      ((A.obj X).ρ g - 1) x ∈ (s.step j.castSucc).obj X := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, one_smul] using
      s.apply_sub_smul_mem X j (e j) g (1 : ℂ) (fun y => by simpa using h j y) hx
  have vanish (j : Fin (n + 1)) :
      ∀ x ∈ (s.step j).obj X, (((A.obj X).ρ g - 1) ^ j.val) x = 0 := by
    induction j using Fin.induction with
    | zero =>
      intro x hx
      rw [s.zero X] at hx
      simpa using (show x = 0 from hx)
    | succ j ih =>
      intro x hx
      rw [Fin.val_succ, pow_succ, Module.End.mul_apply]
      exact ih _ (lower j x hx)
  apply LinearMap.ext
  intro x
  have hx : x ∈ (s.step (Fin.last n)).obj X := by
    rw [s.top X]
    exact Submodule.mem_top
  exact vanish (Fin.last n) x hx

section Intersections

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P Q : ParabolicDatum G} {b : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum P.p P.l P.r P.hp P.hr P.hl P.hmul
    Q.p Q.l Q.r Q.hp Q.hr Q.hl Q.hmul b)
  (hG : IsConnectedReductive G)

include hG in
/-- The source intersection is full when the source Levi is the centralizer of a maximal
split torus. -/
private theorem sourceIntersection_isIso
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hM : SubgroupFunctor.range (P.l ≫ P.p) = torusCentralizer i) :
    IsIso D.p' := by
  let t := D.t ≫ D.l' ≫ D.p' ≫ P.l ≫ P.p
  have ht : SubgroupFunctor.range t ≤ torusCentralizer i := by
    rw [← hM]
    exact SubgroupFunctor.range_comp_le (D.t ≫ D.l' ≫ D.p') (P.l ≫ P.p)
  obtain ⟨f, hf⟩ := hi.exists_factor_of_commute D.isMaximalSplitTorus.1.1 t (by
    intro V x y
    have h := ht V (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    simpa only [Category.id_comp] using h V (𝟙 V) y)
  have htQ : (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') ≫ Q.l ≫ Q.p ≫ (G.innerIso b).hom = t := by
    have h := congrArg (fun f => f ≫ (G.innerIso b).hom) D.targetCommonTorusHom_comp
    simpa only [t, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  have htQmax : IsMaximalSplitTorus
      ((D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') ≫ Q.l ≫ Q.p ≫ (G.innerIso b).hom) :=
    htQ.symm ▸ (show IsMaximalSplitTorus t from D.isMaximalSplitTorus)
  obtain ⟨ξ, hQ, _, _⟩ := exists_cocharacter_parabolic_triple_in_torus
    (p := Q.p ≫ (G.innerIso b).hom) hG (Q.hp.comp_iso _) Q.hl Q.hr parabolicDynamic
    (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') htQmax
  have hle : SubgroupFunctor.range (P.l ≫ P.p) ≤
      SubgroupFunctor.range (Q.p ≫ (G.innerIso b).hom) := by
    rw [hM, hQ, htQ, ← hf, ← Category.assoc]
    exact (torusCentralizer_le_dynamicCentralizer i _).trans (Dynamic.centralizer_le_parabolic _)
  apply IsClosedSubgroup.isIso_of_range_le_range_comp D.hp'.isClosedSubgroup
    (P.hl.isClosedSubgroup.comp P.hp.isClosedSubgroup)
  rw [D.parabolic_eq]
  exact fun V _ hx => ⟨hx, hle V hx⟩

omit [IsAffineHom G.X.hom] in
include hG in
/-- The full rational center of the target Levi lies in the target intersection Levi. -/
private theorem center_le_targetIntersection [Infinite k] :
    Subgroup.center (rationalPoints Q.M) ≤ pointImage (D.lQ' ≫ D.q') := by
  intro x hx
  let R := D.dynamicRealizationOfParabolicDynamic parabolicDynamic hG
  let a := D.targetCommonTorusHom ≫ D.lQ' ≫ D.q'
  let j := a ≫ Q.l ≫ Q.p
  let z := rationalPoints.map (Q.l ≫ Q.p) x
  have hj : IsMaximalSplitTorus j := by
    simpa only [j, a, Category.assoc] using D.targetCommonTorus_isMaximalSplitTorus_ambient
  have hz : z ∈ (torusCentralizer j).rationalPoints := by
    change z ∈ (torusCentralizer j).carrier (Over.mk (𝟙 _))
    rw [torusCentralizer_carrier_base, (normalizerPointsInfiniteField k G hG D.torus j hj.1).2,
      Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    change rationalPoints.map j t * z = z * rationalPoints.map j t
    rw [pointMap_comp_apply a (Q.l ≫ Q.p)]
    exact (map_mul _ _ _).symm.trans
      ((congrArg (rationalPoints.map (Q.l ≫ Q.p))
        (Subgroup.mem_center_iff.mp hx (rationalPoints.map a t))).trans (map_mul _ _ _))
  have hzM : z ∈ (SubgroupFunctor.range (P.l ≫ P.p ≫ (G.innerIso b⁻¹).hom)).rationalPoints := by
    rw [R.sourceLevi]
    simpa only [j, a, Category.assoc] using
      torusCentralizer_le_dynamicCentralizer j
        (CommGroupScheme.groupHom R.sourceCocharacter) (Over.mk (𝟙 _)) hz
  have hz' : z ∈ pointImage (D.lQ' ≫ D.q' ≫ Q.l ≫ Q.p) := by
    rw [pointImage_eq_range_carrier, D.levi_eq']
    exact ⟨⟨x, rfl⟩, hzM⟩
  obtain ⟨y, hy⟩ := hz'
  refine ⟨y, ?_⟩
  have hclosed := Q.hl.isClosedSubgroup.comp Q.hp.isClosedSubgroup
  have : Mono (Q.l ≫ Q.p).hom.hom.left := hclosed.mono
  have : Mono (Q.l ≫ Q.p).hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono (Q.l ≫ Q.p).hom.hom).mp
  change rationalPoints.map (Q.l ≫ Q.p) (rationalPoints.map (D.lQ' ≫ D.q') y) = z
  rw [← pointMap_comp_apply, Category.assoc]
  exact hy

section GradedAction

local instance gradedAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [Infinite k]

include hG in
private theorem piece_acts_trivially_on_center
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hM : SubgroupFunctor.range (P.l ≫ P.p) = torusCentralizer i) :
    letI := leviPointTopology P.l P.hl
    ∀ (σ : SmoothRep.{0, u, 0} ℂ (rationalPoints P.M)),
      (∀ g (x : σ), σ.representation g x = x) →
      ∀ (z : Subgroup.center (rationalPoints Q.M)) (x : D.pieceFunctor.obj σ),
        (D.pieceFunctor.obj σ).ρ z x = x := by
  have := P.hl.isConnectedReductive.isAffineHom
  have := Q.hl.isConnectedReductive.isAffineHom
  let := leviPointTopology P.l P.hl
  let := leviPointTopology Q.l Q.hl
  have := leviPoints_locallyCompactSpace P.p P.l P.hp P.hl
  have := leviPoints_nonarchimedeanGroup P.p P.l P.hp P.hl
  have := leviPoints_locallyCompactSpace Q.p Q.l Q.hp Q.hl
  have := leviPoints_nonarchimedeanGroup Q.p Q.l Q.hp Q.hl
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have : IsIso D.p' := sourceIntersection_isIso D hG i hi hM
  have : IsIso D.l' := D.hl'.isIso_of_isIso_parabolic (p := D.p') P.hl.isConnectedReductive
  intro σ hσ z x
  let τ := (leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ
  have hτ (m : rationalPoints D.M') (v : τ) : τ.representation m v = v := by
    apply (fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' σ).injective
    exact (fullLeviJacquetEquiv_representation
      D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' σ m v).trans (hσ _ _)
  let eL := leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ'
  let A := SmoothRep.pullback eL.symm (SmoothRep.pullback D.e τ)
  have hz := normalizedInductionCentralCharacter_acts
    (isSemidirectDecomposition_pointImage D.q' D.lQ' D.rQ' D.hq'.isClosedSubgroup D.hrQ' D.hmulQ')
    (isClosed_pointImage_comp D.q' D.rQ' D.hq'.isClosedSubgroup D.hrQ'.1.isClosedSubgroup)
    (center_le_targetIntersection D hG) A 1
    (fun m f => by
      change τ.representation (D.e (eL.symm m)) f = _
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using hτ _ f)
    z x
  exact hz.trans (one_smul ℂ x)

end GradedAction

end Intersections

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsT2Field rationalWeightsLocallyCompact

local instance rationalJacquetNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

private theorem represented_minimal_jacquet_unipotent
    (P Q : ParabolicDatum G) (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (hM : SubgroupFunctor.range (P.l ≫ P.p) = torusCentralizer i) :
    ∃ d : ℕ, ∀ z : rationalPoints Q.M, (∀ m, z * m = m * z) →
      ((representedTrivialInducedJacquet P Q).ρ z - 1) ^ d = 0 := by
  let := leviPointTopology P.l P.hl
  have := LocalField.infinite_of_isNonarchimedeanLocalField F
  let σ := (trivialSmoothCharacter (G := rationalPoints P.M)).toSmoothRep
  have hσ (g : rationalPoints P.M) (x : σ) : σ.representation g x = x := by
    exact one_smul ℂ x
  obtain ⟨d, _, _, _, D, perm, s, grades⟩ := representedGeometricLemma.{u, 0} F G hG
    P.P P.M P.U Q.P Q.M Q.U P.p P.l P.r P.hp P.hl P.hr P.hmul
    Q.p Q.l Q.r Q.hp Q.hl Q.hr Q.hmul
  refine ⟨d, fun z hz => ?_⟩
  let zc : Subgroup.center (rationalPoints Q.M) := ⟨z, Subgroup.mem_center_iff.mpr
    (fun m => (hz m).symm)⟩
  exact pow_sub_one_eq_zero_of_filtration s σ z
    (fun j => (Classical.choice (grades j)).app σ)
    (fun j => piece_acts_trivially_on_center (D (perm j)) hG i hi hM σ hσ zc)

end Rational

set_option maxHeartbeats 450000 in
/-- One exponent annihilates the deviations from the identity of every central
point on the normalized Jacquet module of the minimal principal series. -/
theorem rationalMinimalInducedJacquetUnipotent :
    RationalMinimalInducedJacquetUnipotentStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ
  have hM :=
    (ParabolicDatum.range_standard_l_comp_p i ν hG hi hν ∅ (Set.empty_subset _)).trans
      (standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν)
  obtain ⟨d, hd⟩ := represented_minimal_jacquet_unipotent
    (ParabolicDatum.standard i ν hG hi hν ∅ (Set.empty_subset _))
    (ParabolicDatum.standard i ν hG hi hν J hJ) hG i hi hM
  refine ⟨d, rationalMinimalInducedJacquetUnipotent_of_represented i ν hG hi hν J hJ (d := d) ?_⟩
  exact hd

end Langlands.HarishChandraSchwartz
